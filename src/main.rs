use std::borrow::Cow;
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, HashSet};
use std::io::{IsTerminal, Read};
use std::sync::{Arc, LazyLock, Mutex};
use std::time::Duration;

use bytes::{Buf, Bytes};
use clap::Parser;
use colored::{Color, Colorize};
use futures::stream::{Stream, TryStreamExt};
use futures::{AsyncRead, AsyncReadExt, FutureExt, StreamExt};
use gitlab_runner::job::Job;
use gitlab_runner::{CancellableJobHandler, JobResult, Phase, UploadableFile};
use gitlab_runner::{GitlabLayer, RunnerBuilder, outputln};
use handlebars::Handlebars;
use lava_api::job::Health;
use lava_api::joblog::{JobLogError, JobLogLevel, JobLogMsg};
use lava_api::paginator::PaginationError;
use lava_api::test::{ErrorType, PassFail, TestCase};
use lava_api::{Lava, job};
use masker::Masker;
use rand::random;
use serde::{Deserialize, Serialize};
use strum::{Display, EnumString};
use tokio::time::{sleep, timeout};
use tokio_util::sync::CancellationToken;
use tracing::Level;
use tracing::{debug, info};
use tracing_subscriber::filter;
use tracing_subscriber::prelude::*;
use url::Url;

mod throttled;
use throttled::{ThrottledLava, Throttler};

const MASK_PATTERN: &str = "[MASKED]";
/// How many failed test cases to name in a failure summary
const MAX_LISTED_FAILURES: usize = 10;
const DIAGNOSTIC_TIMEOUT: Duration = Duration::from_secs(60);
/// How often in a row a failed request for test results is repeated
const MAX_PAGE_RETRIES: u32 = 3;
/// Wait before repeating a failed request for test results, multiplied by the attempt number
const PAGE_RETRY_DELAY: Duration = Duration::from_secs(2);
/// Length limits, in characters, for text supplied by LAVA in a failure summary
const MAX_TEXT_CHARS: usize = 500;
const MAX_NAME_CHARS: usize = 100;

#[derive(Debug, Default, PartialEq, Eq)]
struct FailureList {
    total: usize,
    names: Vec<String>,
}

impl FailureList {
    fn record(&mut self, name: impl FnOnce() -> String) {
        self.total += 1;
        if self.names.len() < MAX_LISTED_FAILURES {
            self.names.push(name());
        }
    }
}

/// What the LAVA test results say about why a job failed
#[derive(Debug, Default, PartialEq, Eq)]
struct Diagnostic {
    /// Error type of the `lava/job` result, which LAVA records for a job that didn't complete
    error_type: Option<ErrorType>,
    /// Error message of the `lava/job` result
    error_msg: Option<String>,
    /// Failed test cases as `definition/case`, in the order LAVA reports them
    failed: FailureList,
    /// Failed results LAVA recorded for its own actions, which mostly repeat the error above
    failed_actions: FailureList,
}

/// Put text supplied by LAVA on one line and drop control characters
///
/// Error messages can be multi-line (tracebacks, bootloader output) and would otherwise break the
/// one line per fact layout of the failure summary and its styling.
fn single_line(text: &str) -> String {
    text.split_whitespace()
        .map(|word| word.chars().filter(|c| !c.is_control()).collect::<String>())
        .filter(|word| !word.is_empty())
        .collect::<Vec<_>>()
        .join(" ")
}

/// Cut text to at most `max_chars` characters, marking the cut
fn truncate(text: String, max_chars: usize) -> String {
    match text.char_indices().nth(max_chars) {
        Some((end, _)) => format!("{}…", &text[..end]),
        None => text,
    }
}

/// Make text supplied by LAVA fit for the failure summary: masked, on one line, of limited length
///
/// Masking is done on both sides of `single_line`: before, for a secret that itself contains
/// what `single_line` rewrites, and after, as joining lines and dropping control characters can
/// put a secret together that wasn't in the text as LAVA sent it. The text is cut last, a secret
/// cut in half would no longer be masked.
fn lava_text(text: &str, max_chars: usize, mask: &impl Fn(&str) -> String) -> String {
    truncate(mask(&single_line(&mask(text))), max_chars)
}

/// Describe a failed LAVA job in a few lines for the end of the GitLab job log
///
/// `mask` is applied to everything LAVA supplied. The job id and URL are ours and are printed
/// as everywhere else in the log.
fn failure_summary(
    id: i64,
    url: &Url,
    health: Health,
    failure_comment: Option<&str>,
    diagnostic: Option<&Diagnostic>,
    mask: impl Fn(&str) -> String,
) -> Vec<String> {
    let text = |text: &str| Some(lava_text(text, MAX_TEXT_CHARS, &mask)).filter(|t| !t.is_empty());
    let comment = failure_comment.and_then(text);
    // LAVA has an error type "None", which says as little as a missing one.
    let error_type = diagnostic
        .and_then(|d| d.error_type)
        .filter(|error_type| *error_type != ErrorType::None);
    let error = diagnostic.and_then(|d| d.error_msg.as_deref().and_then(text));
    // LAVA's own actions are only worth naming when nothing else explains the failure.
    let failed = match diagnostic {
        Some(d) if d.failed.total > 0 => Some(&d.failed),
        Some(d) if error.is_none() && d.failed_actions.total > 0 => Some(&d.failed_actions),
        _ => None,
    };

    let mut lines = Vec::new();
    match (error_type, error, comment) {
        (Some(error_type), Some(msg), _) => {
            lines.push(format!("LAVA job {id} [{error_type}]: {msg}"))
        }
        (None, Some(msg), _) => lines.push(format!("LAVA job {id}: {msg}")),
        // An error type without a message still says more than the health does.
        (Some(error_type), None, Some(comment)) => {
            lines.push(format!("LAVA job {id} [{error_type}]: {comment}"))
        }
        (Some(error_type), None, None) => lines.push(format!(
            "LAVA job {id} [{error_type}]: finished with health {health}"
        )),
        (None, None, Some(comment)) => lines.push(format!("LAVA job {id} [{health}]: {comment}")),
        // A complete job is only reported here because its test results weren't all passes;
        // naming just the health would read as a success.
        (None, None, None) if failed.is_none() && health == Health::Complete => lines.push(
            format!("LAVA job {id} completed, but not all of its tests passed"),
        ),
        (None, None, None) if failed.is_none() => {
            lines.push(format!("LAVA job {id} finished with health {health}"))
        }
        (None, None, None) => {}
    }
    if let Some(failed) = failed {
        let mut names = failed
            .names
            .iter()
            .map(|name| lava_text(name, MAX_NAME_CHARS, &mask))
            .collect::<Vec<_>>()
            .join(", ");
        let omitted = failed.total - failed.names.len();
        if omitted > 0 {
            names.push_str(&format!(" and {omitted} more"));
        }
        lines.push(format!(
            "LAVA job {id}: {} failed test case{}: {names}",
            failed.total,
            if failed.total == 1 { "" } else { "s" },
        ));
    }
    lines.push(format!("See {url}"));
    lines
}

#[derive(Debug, Clone)]
struct MonitorTimeout {
    next: Duration,
    max: Duration,
}

impl MonitorTimeout {
    fn new(initial: Duration, max: Duration) -> Self {
        MonitorTimeout { next: initial, max }
    }

    fn next_timeout(&mut self) -> Duration {
        self.next().unwrap()
    }
}

impl Iterator for MonitorTimeout {
    type Item = Duration;

    fn next(&mut self) -> Option<Self::Item> {
        let t = self.next.min(self.max);
        self.next = self.max.min(t * 2);

        /* Give a 25% random interval */
        let delta = t / 4;
        Some(t - delta / 2 + delta.mul_f32(random::<f32>()))
    }
}

#[test]
fn monitor_timeout() {
    let max = Duration::from_secs(600);
    let m = MonitorTimeout::new(Duration::from_secs(1), max);

    for (i, current) in m.take(20).enumerate() {
        // The expectation is that for each iteration the timeout median doubles and we start from
        // 1 second; maxing out at the maximum value
        let expected = Duration::from_secs(2u64.pow(i as u32)).min(max);
        assert!(
            current >= expected.mul_f32(0.75) && current < expected.mul_f32(1.25),
            "expected {:?} (+/- 25%), actual {:?}",
            expected,
            current
        );
    }
}

#[derive(Copy, Clone, Display, EnumString)]
#[strum(serialize_all = "lowercase")]
enum LogFormat {
    Pretty,
    Full,
    Compact,
    Json,
}

#[derive(Parser)]
struct Opts {
    #[clap(env = "GITLAB_URL")]
    server: Url,
    #[clap(env = "GITLAB_TOKEN")]
    token: String,
    #[clap(short, long, env = "RUNNER_LOG")]
    log: Option<String>,
    #[clap(long, env = "RUNNER_LOG_FORMAT")]
    log_format: Option<LogFormat>,
    #[clap(
        short,
        long,
        default_value = "4",
        env = "RUNNER_MAX_CONCURRENT_REQUESTS"
    )]
    max_concurrent_requests: usize,
}

#[derive(Deserialize, Debug, Clone)]
struct MonitorJobs {
    jobids: Vec<i64>,
}

#[derive(Clone, Debug, Serialize)]
struct TransformVariables<'a> {
    pub job: BTreeMap<&'a str, &'a str>,
}

#[derive(Debug)]
struct DisplayBox {
    width: usize,
    fg: Color,
}

impl DisplayBox {
    pub fn new(width: usize, fg: Color) -> Self {
        Self::edge(width, true, fg);
        Self { width, fg }
    }

    pub fn line<S, T>(&self, key: S, value: T)
    where
        S: AsRef<str>,
        T: AsRef<str>,
    {
        let kl = key.as_ref().len();
        let vl = value.as_ref().len();
        let total = kl + vl + 6; // two vertical bars, two edge spaces, colon space in centre
        let spacing = self.width.saturating_sub(total);
        let mut spacer = String::new();
        for _ in 0..spacing {
            spacer.push(' ');
        }
        let line = format!("| {}: {}{} |", key.as_ref(), value.as_ref(), spacer).color(self.fg);
        outputln!("{}", line);
    }

    pub fn end(self) {
        Self::edge(self.width, false, self.fg);
    }

    fn edge(width: usize, top: bool, fg: Color) {
        let mut line = String::new();
        let hyphens = width.saturating_sub(2);
        if top {
            line.push('/');
        } else {
            line.push('\\');
        }

        for _ in 0..hyphens {
            line.push('-');
        }

        if top {
            line.push('\\');
        } else {
            line.push('/');
        }
        outputln!("{}", line.color(fg));
    }
}

fn format_value(v: &serde_norway::Value) -> String {
    match v {
        serde_norway::Value::Null => "null".to_string(),
        serde_norway::Value::Bool(b) => b.to_string(),
        serde_norway::Value::Number(n) => n.to_string(),
        serde_norway::Value::String(s) => format!("\"{}\"", s),
        serde_norway::Value::Sequence(seq) => {
            let mut s = String::new();
            s.push_str("[ ");
            let mut first = true;
            for item in seq.iter() {
                if !first {
                    s.push_str(", ");
                    first = false;
                }
                s.push_str(&format_value(item));
            }
            s.push_str(" ]");
            s
        }
        serde_norway::Value::Mapping(map) => {
            let mut s = String::new();
            s.push_str("{ ");
            let mut first = true;
            for (k, v) in map.iter() {
                if !first {
                    s.push_str(", ");
                    first = false;
                }
                s = format!("{}{}: {}", s, format_value(k), format_value(v));
            }
            s.push_str(" }");
            s
        }
        serde_norway::Value::Tagged(t) => format!("{}: {}", t.tag, format_value(&t.value)),
    }
}

fn abbreviate_level(lvl: &JobLogLevel) -> &'static str {
    match lvl {
        JobLogLevel::Debug => "debug =>",
        JobLogLevel::Info => " info =>",
        JobLogLevel::Warning => " WARN =>",
        JobLogLevel::Error => "ERROR =>",
        JobLogLevel::Results => "  res =>",
        JobLogLevel::Target => "  OUT =>",
        JobLogLevel::Input => "   IN <=",
        JobLogLevel::Feedback => "fdbak =>",
        JobLogLevel::Exception => "EXCPT =>",
    }
}

fn color_for_level(lvl: &JobLogLevel) -> Color {
    match lvl {
        JobLogLevel::Debug => Color::Cyan,
        JobLogLevel::Info => Color::BrightBlue,
        JobLogLevel::Warning => Color::Yellow,
        JobLogLevel::Error => Color::Red,
        JobLogLevel::Results => Color::Green,
        JobLogLevel::Target => Color::White,
        JobLogLevel::Input => Color::BrightMagenta,
        JobLogLevel::Feedback => Color::Green,
        JobLogLevel::Exception => Color::BrightRed,
    }
}

/// Whether repeating a failed request for test results can help
///
/// It can't for a reply that doesn't decode or that the server refuses for good, and the
/// paginator ends after a next page link it can't parse.
fn is_transient(error: &PaginationError) -> bool {
    match error {
        PaginationError::ReqWest(e) => {
            !e.is_decode() && !e.status().is_some_and(|status| status.is_client_error())
        }
        PaginationError::ParseNextError(_) => false,
        _ => true,
    }
}

/// Collect the reason LAVA recorded for a failed job from its test results
///
/// Test cases that failed and those with an unknown result are collected: LAVA's JUnit output,
/// which decides whether a complete job passed, counts the latter as errors.
///
/// The results are added to `diagnostic` as they arrive, so that whatever was seen before an
/// error, or before the caller gave up waiting, is still available.
///
/// The paginator repeats the request for a page that failed when it is polled again. That is
/// done up to `MAX_PAGE_RETRIES` times in a row for errors that can be temporary, waiting
/// `retry_delay` times the attempt number in between: LAVA records the `lava/job` result last,
/// so giving up on an earlier page loses the error message.
///
/// TODO: this reads every test case of the job, passes included, one request per page, because
/// lava-api can't filter test cases. For a job with very many results the error message may not
/// be reached within the caller's timeout. Query the `lava/job` result and the failed cases
/// directly once lava-api allows it. lava-api also decodes a page as a whole, so one result it
/// can't decode (an error type it doesn't know, say) ends the collection.
async fn collect_diagnostic<S>(
    mut cases: S,
    diagnostic: &mut Diagnostic,
    retry_delay: Duration,
) -> Result<(), PaginationError>
where
    S: Stream<Item = Result<TestCase, PaginationError>> + Unpin,
{
    let mut retries = 0;
    loop {
        let case = match cases.next().await {
            None => return Ok(()),
            Some(Ok(case)) => {
                retries = 0;
                case
            }
            Some(Err(e)) if retries < MAX_PAGE_RETRIES && is_transient(&e) => {
                retries += 1;
                debug!("retry {} of getting test results: {:?}", retries, e);
                sleep(retry_delay * retries).await;
                continue;
            }
            Some(Err(e)) => return Err(e),
        };
        let note = match case.result {
            PassFail::Fail => "",
            PassFail::Unknown => " (unknown result)",
            PassFail::Pass | PassFail::Skip => continue,
        };
        match case.metadata {
            Some(metadata) if metadata.definition == "lava" && case.name == "job" => {
                diagnostic.error_type = metadata.error_type;
                diagnostic.error_msg = metadata.error_msg;
            }
            Some(metadata) if metadata.definition == "lava" => diagnostic
                .failed_actions
                .record(|| format!("lava/{}{note}", case.name)),
            Some(metadata) => diagnostic
                .failed
                .record(|| format!("{}/{}{note}", metadata.definition, case.name)),
            None => diagnostic.failed.record(|| format!("{}{note}", case.name)),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum JobCancelBehaviour {
    CancelLava,
    LeaveRunning,
}

struct AvailableArtifactStore {
    lava: Arc<ThrottledLava>,
    masker: Arc<Masker>,
}

impl AvailableArtifactStore {
    pub fn new(lava: Arc<ThrottledLava>, masker: Arc<Masker>) -> Self {
        Self { lava, masker }
    }

    pub fn get_log(
        &self,
        id: i64,
    ) -> impl Stream<Item = Result<Bytes, std::io::Error>> + Unpin + Send + '_ {
        self.masker.mask_stream(Box::pin(
            self.lava
                .log(id)
                .map(|x| x.raw())
                .flatten_stream()
                .map_err(std::io::Error::other),
        ))
    }

    pub fn get_junit(
        &self,
        id: i64,
    ) -> impl Stream<Item = Result<Bytes, std::io::Error>> + Unpin + Send + '_ {
        Box::pin(
            self.lava
                .job_results_as_junit(id)
                .map(|res| match res {
                    Ok(s) => s.map_err(std::io::Error::other).boxed(),
                    Err(e) => {
                        futures::stream::once(async move { Err(std::io::Error::other(e)) }).boxed()
                    }
                })
                .flatten_stream(),
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
enum LavaUploadableFileType {
    Log { id: i64 },
    Junit { id: i64 },
}

#[derive(Clone)]
struct LavaUploadableFile {
    store: Arc<AvailableArtifactStore>,
    which: LavaUploadableFileType,
}

impl core::fmt::Debug for LavaUploadableFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.which.fmt(f)
    }
}

impl core::cmp::PartialEq for LavaUploadableFile {
    fn eq(&self, other: &Self) -> bool {
        self.which.eq(&other.which)
    }
}

impl core::cmp::Eq for LavaUploadableFile {}

impl core::cmp::PartialOrd for LavaUploadableFile {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl core::cmp::Ord for LavaUploadableFile {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.which.cmp(&other.which)
    }
}

impl LavaUploadableFile {
    pub fn log(id: i64, store: Arc<AvailableArtifactStore>) -> Self {
        Self {
            which: LavaUploadableFileType::Log { id },
            store,
        }
    }

    pub fn junit(id: i64, store: Arc<AvailableArtifactStore>) -> Self {
        Self {
            which: LavaUploadableFileType::Junit { id },
            store,
        }
    }
}

#[async_trait::async_trait]
impl UploadableFile for LavaUploadableFile {
    type Data<'a> = Box<dyn AsyncRead + Send + Unpin + 'a>;

    fn get_path(&self) -> Cow<'_, str> {
        match self.which {
            LavaUploadableFileType::Log { id } => format!("{}_log.yaml", id).into(),
            LavaUploadableFileType::Junit { id } => format!("{}_junit.xml", id).into(),
        }
    }

    async fn get_data(&self) -> Result<Self::Data<'_>, ()> {
        outputln!("Uploading {}", self.get_path());
        match &self.which {
            LavaUploadableFileType::Log { id } => {
                Ok(Box::new(self.store.get_log(*id).into_async_read()))
            }
            LavaUploadableFileType::Junit { id } => {
                Ok(Box::new(self.store.get_junit(*id).into_async_read()))
            }
        }
    }
}

struct Run {
    lava: Arc<ThrottledLava>,
    store: Arc<AvailableArtifactStore>,
    job: Job,
    url: Url,
    masker: Arc<Masker>,
    ids: Vec<i64>,
    cancel_behaviour: Option<JobCancelBehaviour>,
}

impl Run {
    pub fn new(
        lava: Arc<ThrottledLava>,
        url: Url,
        job: Job,
        cancel_behaviour: Option<JobCancelBehaviour>,
    ) -> Self {
        let masked = job
            .variables()
            .filter(|v| v.masked())
            .map(|v| v.value())
            .collect::<Vec<_>>();
        let masker = Arc::new(Masker::new(&masked, MASK_PATTERN));

        Self {
            lava: lava.clone(),
            store: Arc::new(AvailableArtifactStore::new(lava, masker.clone())),
            url,
            job,
            masker,
            ids: Vec::new(),
            cancel_behaviour,
        }
    }

    async fn find_file(&self, filename: &str) -> Result<Vec<u8>, ()> {
        for d in self.job.dependencies() {
            let artifact = match d.download().await {
                Ok(a) => a,
                Err(e) => {
                    outputln!(
                        "Failed to get artifact from {}: {}",
                        d.name(),
                        self.mask_variables(&e.to_string())
                    );
                    continue;
                }
            };
            if let Some(mut artifact) = artifact {
                let data = if let Some(mut file) = artifact.file(filename) {
                    let mut data = Vec::new();
                    file.read_to_end(&mut data).map(|_| data)
                } else {
                    continue;
                };

                return match data {
                    Ok(data) => Ok(data),
                    Err(e) => {
                        outputln!("Failed to read file from artifact: {}", e);
                        Err(())
                    }
                };
            }
        }
        outputln!("{} not found in artifacts", filename);
        Err(())
    }

    fn url_for_id(&self, id: i64) -> Url {
        let mut url = self.url.clone();
        url.path_segments_mut()
            .unwrap()
            .push("scheduler")
            .push("job")
            .push(&id.to_string());
        url
    }

    async fn submit_definition(&self, definition: &str) -> Result<Vec<i64>, ()> {
        match self.lava.submit_job(definition).await {
            Ok(ids) => {
                for i in &ids {
                    outputln!("Scheduled job: {}", self.url_for_id(*i));
                }
                Ok(ids)
            }
            Err(e) => {
                outputln!("Failed to submit job: {:?}", e);
                Err(())
            }
        }
    }

    fn mask_variables(&self, msg: &str) -> String {
        self.masker.mask_str(msg)
    }

    async fn update_log(&self, id: i64, offset: &mut u64) {
        let mut log = self.lava.log(id).await.start(*offset).log();
        while let Some(entry) = log.next().await {
            match entry {
                Ok(entry) => {
                    match entry.msg {
                        JobLogMsg::Msg(s) => {
                            let fg = color_for_level(&entry.lvl);
                            outputln!(
                                "{} {}",
                                entry.dt.format("%Y-%m-%d %H:%M:%S%.6f"),
                                format!(
                                    "{} {}",
                                    abbreviate_level(&entry.lvl),
                                    self.mask_variables(&s)
                                )
                                .color(fg)
                            );
                        }
                        JobLogMsg::Msgs(ss) => {
                            let fg = color_for_level(&entry.lvl);
                            for s in ss {
                                outputln!(
                                    "{} {}",
                                    entry.dt.format("%Y-%m-%d %H:%M:%S%.6f"),
                                    format!(
                                        "{} {}",
                                        abbreviate_level(&entry.lvl),
                                        self.mask_variables(&s)
                                    )
                                    .color(fg)
                                );
                            }
                        }
                        JobLogMsg::Result(res) => {
                            let fg = match res.result.as_str() {
                                "pass" => color_for_level(&JobLogLevel::Results),
                                "fail" => color_for_level(&JobLogLevel::Error),
                                _ => color_for_level(&JobLogLevel::Warning),
                            };

                            let b = DisplayBox::new(70, fg);
                            b.line("case", self.mask_variables(&res.case));
                            b.line("definition", self.mask_variables(&res.definition));
                            if let Some(ns) = res.namespace {
                                b.line("namespace", self.mask_variables(&ns));
                            }
                            if let Some(level) = res.level {
                                b.line("level", self.mask_variables(&level));
                            }
                            b.line("result", self.mask_variables(&res.result));
                            if let Some(duration) = res.duration {
                                b.line(
                                    "duration",
                                    format!(
                                        "{}.{:0>9}",
                                        duration.as_secs(),
                                        duration.subsec_nanos()
                                    ),
                                );
                            }
                            for (k, v) in res.extra.iter() {
                                b.line(
                                    self.mask_variables(k),
                                    self.mask_variables(&format_value(v)),
                                );
                            }
                            b.end();
                        }
                    }
                    *offset += 1;
                }
                Err(JobLogError::NoData) => (),
                Err(JobLogError::ParseError(s, e)) => {
                    outputln!(
                        "{}",
                        format!(
                            "Couldn't parse {} - {}",
                            self.mask_variables(s.trim_end()),
                            self.mask_variables(&e.to_string())
                        )
                        .bright_red()
                    );
                    *offset += 1;
                }
                Err(e) => {
                    debug!("failed to get update from log: {:?}", e);
                    break;
                }
            }
        }
    }

    async fn cancel_job(
        &self,
        default_behaviour: JobCancelBehaviour,
        job_id: i64,
    ) -> Result<(), job::CancellationError> {
        match self.cancel_behaviour.unwrap_or(default_behaviour) {
            JobCancelBehaviour::CancelLava => {
                info!("Cancelling LAVA job {}", job_id);
                self.lava.cancel_job(job_id).await
            }
            JobCancelBehaviour::LeaveRunning => {
                info!("Not cancelling LAVA job {}, leaving it running", job_id);
                Ok(())
            }
        }
    }

    /// Print where to find a LAVA job that failed
    fn print_job_link(&self, id: i64) {
        let line = format!("See {}", self.url_for_id(id));
        outputln!("{}", line.bright_red().bold());
    }

    /// Print why a LAVA job failed and where to find it
    ///
    /// This is only for the reader of the log. A failure to look up the details is reported and
    /// otherwise ignored. The lookup is skipped for a cancelled job and given up when the GitLab
    /// job is cancelled, so that cancelling doesn't have to wait for it.
    async fn report_failure(
        &self,
        id: i64,
        health: Health,
        failure_comment: Option<&str>,
        cancel_token: &CancellationToken,
    ) {
        let mut diagnostic = Diagnostic::default();
        if health != Health::Canceled {
            let lookup = async {
                // Get the request permit first: time spent queueing behind other requests of
                // this runner says nothing about LAVA and must not use up the time allowed for
                // the lookup.
                let cases = self.lava.test_cases(id).await;
                timeout(
                    DIAGNOSTIC_TIMEOUT,
                    collect_diagnostic(cases, &mut diagnostic, PAGE_RETRY_DELAY),
                )
                .await
            };
            match cancel_token.run_until_cancelled(lookup).await {
                None | Some(Ok(Ok(()))) => {}
                Some(Ok(Err(e))) => {
                    outputln!(
                        "Failed to get all test results of LAVA job {}, the summary may be incomplete: {}",
                        id,
                        self.mask_variables(&e.to_string())
                    );
                }
                Some(Err(_)) => {
                    outputln!(
                        "Timed out getting test results of LAVA job {}, the summary may be incomplete",
                        id
                    );
                }
            }
        }

        let url = self.url_for_id(id);
        let mask = |text: &str| self.mask_variables(text);
        for line in failure_summary(id, &url, health, failure_comment, Some(&diagnostic), mask) {
            outputln!("{}", line.bright_red().bold());
        }
    }

    async fn wait_for_jobs(
        &self,
        mut ids: HashSet<i64>,
        cancel_token: &CancellationToken,
        cancel_behaviour: JobCancelBehaviour,
    ) -> JobResult {
        let mut running = HashSet::new();
        let mut failures = false;
        let mut timeout = MonitorTimeout::new(Duration::from_secs(30), Duration::from_secs(600));
        loop {
            if ids.is_empty() {
                break;
            }

            let mut builder = self.lava.jobs().await;
            for id in &ids {
                builder = builder.id(*id);
            }

            let mut jobs = builder.query();
            let mut failed = Vec::new();
            let mut to_cancel = Vec::new();
            while let Some(job) = jobs.next().await {
                let job = match job {
                    Ok(job) => job,
                    Err(e) => {
                        // The paginator repeats a failed request when polled again and so never
                        // ends while LAVA is unreachable. Leave that to the next poll, after
                        // the usual wait.
                        outputln!(
                            "Failed to check status: {}",
                            self.mask_variables(&e.to_string())
                        );
                        break;
                    }
                };
                if job.state == job::State::Running && !running.contains(&job.id) {
                    outputln!("{} is running", self.url_for_id(job.id));
                    running.insert(job.id);
                }
                if job.state == job::State::Finished {
                    ids.remove(&job.id);
                    if job.health == Health::Complete {
                        outputln!("{} successfully finished", self.url_for_id(job.id));
                    } else {
                        outputln!("{} UNSUCCESSFULL!", self.url_for_id(job.id));
                        failures = true;
                        failed.push((job.id, job.health, job.failure_comment.clone()));
                    }
                }
                if cancel_token.is_cancelled() {
                    match job.state {
                        job::State::Finished | job::State::Canceling => {}
                        _ => to_cancel.push(job.id),
                    }
                }
            }

            // The job query holds a request permit, release it before making further requests:
            // holding two permits at once can deadlock.
            drop(jobs);

            // Cancelling goes first, it shouldn't have to wait for the failure reports.
            for id in to_cancel {
                match self.cancel_job(cancel_behaviour, id).await {
                    Ok(_) => {
                        outputln!("Cancelled LAVA job {}", id);
                        ids.remove(&id);
                    }
                    Err(e) => {
                        outputln!("Error cancelling LAVA job {}: {}", id, e);
                    }
                }
            }

            // Look the failures up concurrently so that many jobs failing at once don't hold up
            // the next poll for long; the throttler limits how many lookups run at a time. Each
            // report prints its lines in one go, so they don't mix.
            futures::future::join_all(failed.iter().map(|(id, health, comment)| {
                self.report_failure(*id, *health, comment.as_deref(), cancel_token)
            }))
            .await;

            sleep(timeout.next_timeout()).await;
        }

        if failures { Err(()) } else { Ok(()) }
    }

    async fn all_tests_passed(&self, id: i64) -> Result<bool, ()> {
        let mut bytes = Vec::new();
        Box::pin(
            self.lava
                .job_results_as_junit(id)
                .await
                .map_err(|e| {
                    outputln!(
                        "Failed to get job results: {}",
                        self.mask_variables(&e.to_string())
                    );
                })?
                .map_err(std::io::Error::other),
        )
        .into_async_read()
        .read_to_end(&mut bytes)
        .await
        .map_err(|e| {
            outputln!(
                "Failed to get job results: {}",
                self.mask_variables(&e.to_string())
            );
        })?;

        let ts = junit_parser::from_reader(bytes.reader()).map_err(|e| {
            outputln!(
                "Failed to parse job results: {}",
                self.mask_variables(&e.to_string())
            );
        })?;

        Ok(ts.errors == 0 && ts.failures == 0)
    }

    async fn get_job(&self, id: i64) -> Result<Option<job::Job>, PaginationError> {
        let mut jobs = self.lava.jobs().await.id(id).query();
        jobs.try_next().await
    }

    async fn follow_job(
        &self,
        id: i64,
        cancel_token: &CancellationToken,
        cancel_behaviour: JobCancelBehaviour,
    ) -> JobResult {
        let mut offset = 0u64;
        loop {
            // `get_job` is a separate function in order to limit the
            // scope of the permit it obtains via the throttled Lava
            // interface. This is important because within the loop we
            // will obtain a second permit for access to the logs for
            // this job. Owning two permits simultaneously can cause
            // deadlocks in this version of the throttling API.
            match self.get_job(id).await {
                Ok(Some(job)) => {
                    match job.state {
                        job::State::Running => self.update_log(id, &mut offset).await,
                        job::State::Finished => {
                            /* Get the final part of the log if any */
                            self.update_log(id, &mut offset).await;

                            if job.health == Health::Complete {
                                match self.all_tests_passed(id).await {
                                    Ok(true) => {
                                        return Ok(());
                                    }
                                    Ok(false) => {
                                        outputln!("Job completed with errors");
                                        self.report_failure(
                                            id,
                                            job.health,
                                            job.failure_comment.as_deref(),
                                            cancel_token,
                                        )
                                        .await;
                                        return Err(());
                                    }
                                    Err(_) => {
                                        // Why is already printed, and it isn't a test failure.
                                        self.print_job_link(id);
                                        return Err(());
                                    }
                                };
                            } else {
                                outputln!("Job didn't complete correctly");
                                self.report_failure(
                                    id,
                                    job.health,
                                    job.failure_comment.as_deref(),
                                    cancel_token,
                                )
                                .await;
                                return Err(());
                            }
                        }
                        _ => (),
                    }
                    self.update_log(id, &mut offset).await;
                    if cancel_token.is_cancelled() {
                        match job.state {
                            job::State::Finished | job::State::Canceling => {}
                            _ => match self.cancel_job(cancel_behaviour, id).await {
                                Ok(_) => {
                                    outputln!("Cancelled LAVA job {}", id);
                                    return Ok(());
                                }
                                Err(e) => {
                                    outputln!("Error cancelling LAVA job {}: {}", id, e);
                                }
                            },
                        }
                    }
                }
                Ok(None) => {
                    outputln!("Lava doesn't know about our job?");
                    return Err(());
                }
                Err(e) => {
                    outputln!("Failed to check status: {:?}", e);
                }
            }

            sleep(Duration::from_secs(20)).await;
        }
    }

    fn transform(&self, definition: String) -> Result<String, ()> {
        let mut handlebars = Handlebars::new();
        handlebars.set_strict_mode(true);
        handlebars
            .register_template_string("definition", definition)
            .map_err(|e| {
                outputln!("Failed to parse template: {}", e);
            })?;

        let mappings = TransformVariables {
            job: self
                .job
                .variables()
                .map(|var| (var.key(), var.value()))
                .collect(),
        };
        handlebars.render("definition", &mappings).map_err(|e| {
            outputln!("Failed to substitute in template: {}", e);
        })
    }

    async fn command(&mut self, command: &str, cancel_token: &CancellationToken) -> JobResult {
        outputln!("> {}", command);
        let mut p = command.split_whitespace();
        if let Some(cmd) = p.next() {
            debug!("command: >{}<", cmd);
            match cmd {
                "submit" => {
                    if let Some(filename) = p.next() {
                        let data = self.find_file(filename).await?;
                        let definition = match String::from_utf8(data) {
                            Ok(data) => self.transform(data)?,
                            Err(_) => {
                                outputln!("Job definition is not utf-8");
                                return Err(());
                            }
                        };
                        let ids = self.submit_definition(&definition).await?;
                        self.ids.extend(&ids);
                        self.follow_job(ids[0], cancel_token, JobCancelBehaviour::CancelLava)
                            .await
                    } else {
                        outputln!("Missing file to submit");
                        Err(())
                    }
                }
                "monitor-file" => {
                    if let Some(filename) = p.next() {
                        let data = self.find_file(filename).await?;
                        let jobs = match serde_json::from_slice::<MonitorJobs>(&data) {
                            Ok(jobs) if jobs.jobids.is_empty() => {
                                outputln!("No job ids in json file!");
                                return Err(());
                            }
                            Ok(jobs) => jobs,
                            Err(e) => {
                                outputln!("Failed to parse job file: {}", e);
                                return Err(());
                            }
                        };
                        self.ids.extend(&jobs.jobids);
                        let mut ids = HashSet::new();
                        ids.extend(&jobs.jobids);

                        outputln!("Waiting for jobs:");
                        for id in &ids {
                            outputln!("\t* {}", self.url_for_id(*id));
                        }
                        outputln!("");
                        self.wait_for_jobs(ids, cancel_token, JobCancelBehaviour::LeaveRunning)
                            .await
                    } else {
                        outputln!("Missing file to submit");
                        Err(())
                    }
                }
                _ => {
                    outputln!("Unknown command");
                    Err(())
                }
            }
        } else {
            outputln!("empty command");
            Err(())
        }
    }
}

#[async_trait::async_trait]
impl CancellableJobHandler<LavaUploadableFile> for Run {
    async fn step(
        &mut self,
        script: &[String],
        _phase: Phase,
        cancel_token: &CancellationToken,
    ) -> JobResult {
        for command in script {
            self.command(command, cancel_token).await?;
        }

        Ok(())
    }

    async fn get_uploadable_files(
        &mut self,
    ) -> Result<Box<dyn Iterator<Item = LavaUploadableFile> + Send>, ()> {
        let mut available_files = Vec::new();
        for id in &self.ids {
            available_files.push(LavaUploadableFile::log(*id, self.store.clone()));
            available_files.push(LavaUploadableFile::junit(*id, self.store.clone()));
        }
        Ok(Box::new(available_files.into_iter()))
    }
}

type LavaMap = Arc<Mutex<BTreeMap<(String, String), Arc<ThrottledLava>>>>;

static LAVA_MAP: LazyLock<LavaMap> = LazyLock::new(|| Arc::new(Mutex::new(BTreeMap::new())));
static MAX_CONCURRENT_REQUESTS: LazyLock<Arc<Mutex<usize>>> =
    LazyLock::new(|| Arc::new(Mutex::new(20)));

async fn new_job(job: Job) -> Result<impl CancellableJobHandler<LavaUploadableFile>, ()> {
    info!("Creating new run for job: {}", job.id());
    let lava_url = match job.variable("LAVA_URL") {
        Some(u) => u,
        None => {
            outputln!("Missing LAVA_URL");
            return Err(());
        }
    };

    let lava_token = match job.variable("LAVA_TOKEN") {
        Some(t) => t,
        None => {
            outputln!("Missing LAVA_TOKEN");
            return Err(());
        }
    };

    let url = match lava_url.value().parse() {
        Ok(u) => u,
        Err(e) => {
            outputln!("LAVA_URL is invalid: {}", e);
            return Err(());
        }
    };

    let cancel_behaviour = match job
        .variable("LAVA_CANCELLATION")
        .map(|v| match v.value().to_lowercase().as_str() {
            "cancel" => Ok(JobCancelBehaviour::CancelLava),
            "ignore" => Ok(JobCancelBehaviour::LeaveRunning),
            _ => {
                outputln!(
                    "Bad value '{}' for LAVA_CANCELLATION: must be 'ignore' or 'cancel'",
                    v.value()
                );
                Err(())
            }
        })
        .transpose()
    {
        Ok(v) => v,
        Err(_) => return Err(()),
    };

    let max_requests = {
        let m = MAX_CONCURRENT_REQUESTS.lock().unwrap();
        *m
    };

    let lava = match LAVA_MAP
        .lock()
        .unwrap()
        .entry((lava_url.value().to_string(), lava_token.value().to_string()))
    {
        Entry::Occupied(o) => o.get().clone(),
        Entry::Vacant(v) => {
            match Lava::new(lava_url.value(), Some(lava_token.value().to_string())) {
                Ok(lava) => {
                    let throttled =
                        Arc::new(ThrottledLava::new(lava, Throttler::new(max_requests)));
                    v.insert(throttled.clone());
                    throttled
                }
                Err(e) => {
                    outputln!("Failed to setup lava: {}", e);
                    return Err(());
                }
            }
        }
    };

    Ok(Run::new(lava, url, job, cancel_behaviour))
}

#[tokio::main]
async fn main() {
    let opts = Opts::parse();
    let dir = tempfile::tempdir().unwrap();

    let (layer, jobs) = GitlabLayer::new();

    let log_targets = if let Some(log) = opts.log {
        log.parse::<filter::Targets>()
            .unwrap()
            .with_target("gitlab_runner::gitlab::job", Level::ERROR)
    } else {
        filter::Targets::new().with_default(Level::INFO)
    };

    let log_format = opts.log_format.unwrap_or_else(|| {
        if std::io::stdout().is_terminal() {
            LogFormat::Pretty
        } else {
            LogFormat::Json
        }
    });

    let fmt = tracing_subscriber::fmt::Layer::new();
    let fmt = match log_format {
        LogFormat::Full => fmt.boxed(),
        LogFormat::Pretty => fmt.pretty().boxed(),
        LogFormat::Compact => fmt.compact().boxed(),
        LogFormat::Json => fmt.json().boxed(),
    };

    tracing_subscriber::Registry::default()
        .with(layer)
        .with(fmt.with_filter(log_targets))
        .init();

    {
        let mut max_requests = MAX_CONCURRENT_REQUESTS.lock().unwrap();
        *max_requests = opts.max_concurrent_requests;
        info!(
            "Setting max concurrent requests to {}",
            opts.max_concurrent_requests
        );
    }

    let mut runner = RunnerBuilder::new(opts.server, opts.token, dir.path(), jobs)
        .version(env!("CARGO_PKG_VERSION"))
        .revision(
            option_env!("VERGEN_GIT_SHA")
                .map(|sha| {
                    if option_env!("VERGEN_GIT_DIRTY") == Some("true") {
                        format!("{}-dirty", sha)
                    } else {
                        sha.to_string()
                    }
                })
                .unwrap_or_else(|| "-".to_string()),
        )
        .architecture("gitlab-runner-rs")
        .platform(env!("CARGO_BIN_NAME"))
        .build()
        .await;

    runner
        .run(new_job, 64)
        .await
        .expect("Couldn't pick up jobs");
}

#[cfg(test)]
mod failure_summary_tests {
    use super::*;

    fn url() -> Url {
        "https://lava.example.com/scheduler/job/42".parse().unwrap()
    }

    fn see() -> String {
        "See https://lava.example.com/scheduler/job/42".to_string()
    }

    fn summary(
        id: i64,
        url: &Url,
        health: Health,
        failure_comment: Option<&str>,
        diagnostic: Option<&Diagnostic>,
    ) -> Vec<String> {
        failure_summary(id, url, health, failure_comment, diagnostic, str::to_owned)
    }

    fn failures(names: &[&str]) -> FailureList {
        let mut list = FailureList::default();
        for name in names {
            list.record(|| (*name).to_owned());
        }
        list
    }

    #[test]
    fn job_error_wins_over_comment() {
        let diagnostic = Diagnostic {
            error_type: Some(ErrorType::Infrastructure),
            error_msg: Some("matched a bootloader error message: 'File not found' (7)".to_string()),
            failed_actions: failures(&["lava/uboot-action"]),
            ..Default::default()
        };
        assert_eq!(
            summary(
                42,
                &url(),
                Health::Incomplete,
                Some("edited later"),
                Some(&diagnostic)
            ),
            [
                "LAVA job 42 [Infrastructure]: matched a bootloader error message: \
                 'File not found' (7)"
                    .to_string(),
                see()
            ]
        );
    }

    #[test]
    fn comment_is_used_without_job_error() {
        assert_eq!(
            summary(
                42,
                &url(),
                Health::Incomplete,
                Some(" board fell over \n"),
                Some(&Diagnostic::default())
            ),
            [
                "LAVA job 42 [Incomplete]: board fell over".to_string(),
                see()
            ]
        );
    }

    #[test]
    fn blank_job_errors_allow_comment_and_action_fallbacks() {
        for msg in ["", " \t\n"] {
            let diagnostic = Diagnostic {
                error_type: Some(ErrorType::Infrastructure),
                error_msg: Some(msg.to_owned()),
                failed_actions: failures(&["lava/boot"]),
                ..Default::default()
            };
            assert_eq!(
                summary(
                    42,
                    &url(),
                    Health::Incomplete,
                    Some("boot failed"),
                    Some(&diagnostic)
                ),
                [
                    "LAVA job 42 [Infrastructure]: boot failed".to_string(),
                    "LAVA job 42: 1 failed test case: lava/boot".to_string(),
                    see()
                ]
            );
        }
    }

    #[test]
    fn error_type_without_message_is_kept() {
        let diagnostic = Diagnostic {
            error_type: Some(ErrorType::Infrastructure),
            ..Default::default()
        };
        assert_eq!(
            summary(42, &url(), Health::Incomplete, None, Some(&diagnostic)),
            [
                "LAVA job 42 [Infrastructure]: finished with health Incomplete".to_string(),
                see()
            ]
        );
    }

    #[test]
    fn error_type_none_is_not_shown() {
        let mut diagnostic = Diagnostic {
            error_type: Some(ErrorType::None),
            error_msg: Some("something broke".to_string()),
            ..Default::default()
        };
        assert_eq!(
            summary(42, &url(), Health::Incomplete, None, Some(&diagnostic)),
            ["LAVA job 42: something broke".to_string(), see()]
        );

        diagnostic.error_msg = None;
        assert_eq!(
            summary(
                42,
                &url(),
                Health::Incomplete,
                Some("oops"),
                Some(&diagnostic)
            ),
            ["LAVA job 42 [Incomplete]: oops".to_string(), see()]
        );
    }

    #[test]
    fn secrets_are_masked_however_lava_formats_them() {
        let mask = |text: &str| text.replace("abc def", MASK_PATTERN);
        for msg in [
            "abc def",
            "abc\ndef",
            "abc  def",
            "abc \x1b def",
            "a\x07bc def",
        ] {
            let diagnostic = Diagnostic {
                error_msg: Some(format!("token {msg} rejected")),
                failed: failures(&[&format!("0_t/{msg}")]),
                ..Default::default()
            };
            assert_eq!(
                failure_summary(
                    42,
                    &url(),
                    Health::Incomplete,
                    Some(msg),
                    Some(&diagnostic),
                    mask
                ),
                [
                    "LAVA job 42: token [MASKED] rejected".to_string(),
                    "LAVA job 42: 1 failed test case: 0_t/[MASKED]".to_string(),
                    see()
                ],
                "{msg:?}"
            );
            assert_eq!(
                failure_summary(42, &url(), Health::Incomplete, Some(msg), None, mask),
                ["LAVA job 42 [Incomplete]: [MASKED]".to_string(), see()],
                "{msg:?}"
            );
        }

        // A secret that spans lines itself is found before the lines are joined.
        let mask = |text: &str| text.replace("abc\ndef", MASK_PATTERN);
        assert_eq!(
            failure_summary(42, &url(), Health::Incomplete, Some("abc\ndef"), None, mask),
            ["LAVA job 42 [Incomplete]: [MASKED]".to_string(), see()]
        );
    }

    #[test]
    fn long_text_is_cut() {
        let diagnostic = Diagnostic {
            error_msg: Some("é".repeat(MAX_TEXT_CHARS + 1)),
            failed: failures(&[&"n".repeat(MAX_NAME_CHARS + 1), "short"]),
            ..Default::default()
        };
        assert_eq!(
            summary(42, &url(), Health::Incomplete, None, Some(&diagnostic)),
            [
                format!("LAVA job 42: {}…", "é".repeat(MAX_TEXT_CHARS)),
                format!(
                    "LAVA job 42: 2 failed test cases: {}…, short",
                    "n".repeat(MAX_NAME_CHARS)
                ),
                see()
            ]
        );

        let exact = "x".repeat(MAX_TEXT_CHARS);
        assert_eq!(
            summary(42, &url(), Health::Incomplete, Some(&exact), None)[0],
            format!("LAVA job 42 [Incomplete]: {exact}")
        );
    }

    #[test]
    fn health_is_the_fallback() {
        for diagnostic in [None, Some(&Diagnostic::default())] {
            assert_eq!(
                summary(42, &url(), Health::Canceled, Some("  "), diagnostic),
                [
                    "LAVA job 42 finished with health Canceled".to_string(),
                    see()
                ]
            );
        }
    }

    #[test]
    fn failed_tests_of_a_complete_job() {
        let diagnostic = Diagnostic {
            failed: failures(&["0_dmesg/emerg"]),
            ..Default::default()
        };
        assert_eq!(
            summary(42, &url(), Health::Complete, None, Some(&diagnostic)),
            [
                "LAVA job 42: 1 failed test case: 0_dmesg/emerg".to_string(),
                see()
            ]
        );
    }

    #[test]
    fn job_error_and_failed_tests() {
        let diagnostic = Diagnostic {
            error_type: Some(ErrorType::Test),
            error_msg: Some("lava-test-shell timed out".to_string()),
            failed: failures(&["1_kselftest/a", "1_kselftest/b"]),
            failed_actions: failures(&["lava/lava-test-shell"]),
        };
        assert_eq!(
            summary(42, &url(), Health::Incomplete, None, Some(&diagnostic)),
            [
                "LAVA job 42 [Test]: lava-test-shell timed out".to_string(),
                "LAVA job 42: 2 failed test cases: 1_kselftest/a, 1_kselftest/b".to_string(),
                see()
            ]
        );
    }

    #[test]
    fn failed_actions_are_the_last_resort() {
        let mut diagnostic = Diagnostic {
            failed_actions: failures(&["lava/0_dmesg"]),
            ..Default::default()
        };
        assert_eq!(
            summary(42, &url(), Health::Complete, None, Some(&diagnostic)),
            [
                "LAVA job 42: 1 failed test case: lava/0_dmesg".to_string(),
                see()
            ]
        );

        diagnostic.failed = failures(&["0_dmesg/warn"]);
        assert_eq!(
            summary(42, &url(), Health::Complete, None, Some(&diagnostic)),
            [
                "LAVA job 42: 1 failed test case: 0_dmesg/warn".to_string(),
                see()
            ]
        );
    }

    #[test]
    fn complete_job_without_details_does_not_read_as_success() {
        for diagnostic in [None, Some(&Diagnostic::default())] {
            assert_eq!(
                summary(42, &url(), Health::Complete, None, diagnostic),
                [
                    "LAVA job 42 completed, but not all of its tests passed".to_string(),
                    see()
                ]
            );
        }
    }

    #[test]
    fn lava_text_is_put_on_one_line() {
        let diagnostic = Diagnostic {
            error_type: Some(ErrorType::Bug),
            error_msg: Some("Traceback:\r\n  File \"x.py\"\n\x1b[31mKeyError\x07\n".to_string()),
            failed: failures(&["0_a/b\nc"]),
            ..Default::default()
        };
        assert_eq!(
            summary(42, &url(), Health::Incomplete, None, Some(&diagnostic)),
            [
                "LAVA job 42 [Bug]: Traceback: File \"x.py\" [31mKeyError".to_string(),
                "LAVA job 42: 1 failed test case: 0_a/b c".to_string(),
                see()
            ]
        );
        assert_eq!(
            summary(
                42,
                &url(),
                Health::Incomplete,
                Some("line one\nline two"),
                None
            ),
            [
                "LAVA job 42 [Incomplete]: line one line two".to_string(),
                see()
            ]
        );
    }

    fn case(definition: &str, name: &str, error_msg: Option<&str>) -> TestCase {
        TestCase {
            id: 1,
            name: name.to_string(),
            unit: String::new(),
            result: PassFail::Fail,
            measurement: None,
            metadata: Some(lava_api::test::Metadata {
                definition: definition.to_string(),
                case: name.to_string(),
                result: PassFail::Fail,
                namespace: None,
                level: None,
                duration: None,
                extra: None,
                error_msg: error_msg.map(str::to_string),
                error_type: error_msg.map(|_| ErrorType::Infrastructure),
            }),
            suite: 1,
            start_log_line: None,
            end_log_line: None,
            test_set: None,
            logged: chrono::Utc::now(),
            resource_uri: String::new(),
        }
    }

    #[tokio::test]
    async fn results_before_an_error_are_kept() {
        let cases = futures::stream::iter([
            Ok(case("lava", "job", Some("boot failed"))),
            Ok(case("0_dmesg", "emerg", None)),
            Err(PaginationError::ParseNextError(url::ParseError::EmptyHost)),
            Ok(case("0_dmesg", "alert", None)),
        ]);
        let mut diagnostic = Diagnostic::default();
        assert!(
            collect_diagnostic(cases, &mut diagnostic, Duration::ZERO)
                .await
                .is_err()
        );
        assert_eq!(
            diagnostic,
            Diagnostic {
                error_type: Some(ErrorType::Infrastructure),
                error_msg: Some("boot failed".to_string()),
                failed: failures(&["0_dmesg/emerg"]),
                ..Default::default()
            }
        );
    }

    #[tokio::test]
    async fn results_before_a_timeout_are_kept() {
        let cases = futures::stream::iter([Ok(case("0_dmesg", "emerg", None))])
            .chain(futures::stream::pending());
        let mut diagnostic = Diagnostic::default();
        let collect = collect_diagnostic(cases, &mut diagnostic, Duration::ZERO);
        assert!(timeout(Duration::from_millis(10), collect).await.is_err());
        assert_eq!(diagnostic.failed, failures(&["0_dmesg/emerg"]));
    }

    #[tokio::test]
    async fn temporary_errors_are_retried() {
        let error = || Err(PaginationError::RedirectMissing);
        let cases = futures::stream::iter([
            Ok(case("0_dmesg", "emerg", None)),
            error(),
            error(),
            error(),
            Ok(case("0_dmesg", "alert", None)),
            error(),
            Ok(case("lava", "job", Some("boot failed"))),
        ]);
        let mut diagnostic = Diagnostic::default();
        assert!(
            collect_diagnostic(cases, &mut diagnostic, Duration::ZERO)
                .await
                .is_ok()
        );
        assert_eq!(
            diagnostic,
            Diagnostic {
                error_type: Some(ErrorType::Infrastructure),
                error_msg: Some("boot failed".to_string()),
                failed: failures(&["0_dmesg/emerg", "0_dmesg/alert"]),
                ..Default::default()
            }
        );
    }

    #[tokio::test]
    async fn retries_are_limited() {
        let cases = futures::stream::iter(
            std::iter::repeat_with(|| Err(PaginationError::RedirectMissing))
                .take(MAX_PAGE_RETRIES as usize + 1),
        )
        .chain(futures::stream::iter([Ok(case("0_dmesg", "emerg", None))]));
        let mut diagnostic = Diagnostic::default();
        assert!(
            collect_diagnostic(cases, &mut diagnostic, Duration::ZERO)
                .await
                .is_err()
        );
        assert_eq!(diagnostic, Diagnostic::default());
    }

    #[tokio::test]
    async fn unknown_results_are_collected() {
        let mut unknown = case("0_dmesg", "crit", None);
        unknown.result = PassFail::Unknown;
        let mut passed = case("0_dmesg", "alert", None);
        passed.result = PassFail::Pass;
        let mut skipped = case("0_dmesg", "warn", None);
        skipped.result = PassFail::Skip;
        let cases = futures::stream::iter([Ok(unknown), Ok(passed), Ok(skipped)]);
        let mut diagnostic = Diagnostic::default();
        assert!(
            collect_diagnostic(cases, &mut diagnostic, Duration::ZERO)
                .await
                .is_ok()
        );
        assert_eq!(
            summary(42, &url(), Health::Complete, None, Some(&diagnostic)),
            [
                "LAVA job 42: 1 failed test case: 0_dmesg/crit (unknown result)".to_string(),
                see()
            ]
        );
    }

    #[test]
    fn long_lists_are_cut() {
        let mut diagnostic = Diagnostic::default();
        for i in 0..MAX_LISTED_FAILURES + 3 {
            diagnostic.failed.record(|| format!("t/{i}"));
        }
        assert_eq!(diagnostic.failed.names.len(), MAX_LISTED_FAILURES);
        let summary = summary(42, &url(), Health::Complete, None, Some(&diagnostic));
        assert_eq!(
            summary[0],
            "LAVA job 42: 13 failed test cases: t/0, t/1, t/2, t/3, t/4, t/5, t/6, t/7, t/8, t/9 \
             and 3 more"
        );
    }
}

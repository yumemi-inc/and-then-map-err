//! # `and_then_map_err`
//!
//! `and_then_map_err` provides traits for chaining `Result` operations
//! with different error types without needing intermediate `map_err` calls.
//! This allows more flexible error handling by converting error types
//! between chained operations.
//!
//! ## Features
//!
//! - `AndThenMapErr` trait: Enables chaining `Result` operations where the error type can be converted.
//! - `MapErrAndThen` trait: Enables mapping the error type of initial `Result` before chaining another operation.
//!
//! ## Examples
//!
//! ```rust
//! use thiserror::Error;
//! use and_then_map_err::{AndThenMapErr, MapErrAndThen};
//!
//! #[derive(Error, Debug, Eq, PartialEq)]
//! pub enum ParentError {
//!     #[error("parent error: {0}")]
//!     Parent(String),
//!     #[error("parent error from child error: {0}")]
//!     FromChild(#[from] ChildError),
//! }
//!
//! #[derive(Error, Debug, Eq, PartialEq)]
//! pub enum ChildError {
//!     #[error("child error: {0}")]
//!     Child(String),
//! }
//!
//! let result_or_parent_err: Result<(), ParentError> = Ok(());
//! let new_result_or_parent_err: Result<(), ParentError> = result_or_parent_err.and_then_map_err(|x| {
//!     Err(ChildError::Child("error occurred afterwards".to_string()))
//! });
//! assert_eq!(new_result_or_parent_err, Err(ParentError::FromChild(ChildError::Child("error occurred afterwards".to_string()))));
//!
//! let result_or_child_err: Result<(), ChildError> = Err(ChildError::Child("initial error".to_string()));
//! let new_result_or_parent_err: Result<(), ParentError> = result_or_child_err.map_err_and_then(|x| {
//!     Ok(x)
//! });
//! assert_eq!(new_result_or_parent_err, Err(ParentError::FromChild(ChildError::Child("initial error".to_string()))));
//! ```

/// The `and_then_map_err` trait allows for error mapping on `Result` types.
/// This trait converts an error in the result of the operation `Result<U, E2>`
/// to a different error type `E1` if the initial operation fails.
///
/// # Examples
///
/// ```
/// use thiserror::Error;
/// use and_then_map_err::AndThenMapErr;
///
/// #[derive(Error, Debug, Eq, PartialEq)]
/// pub enum ParentError {
///     #[error("parent error: {0}")]
///     Parent(String),
///     #[error("parent error from child error: {0}")]
///     FromChild(#[from] ChildError),
/// }
///
/// #[derive(Error, Debug, Eq, PartialEq)]
/// pub enum ChildError {
///     #[error("child error: {0}")]
///     Child(String),
/// }
///
/// // Case 1: The original result is Ok and the operation succeeds.
/// let result: Result<(), ParentError> = Ok(());
/// let new_result: Result<(), ParentError> = result.and_then_map_err(|x| -> Result<(), ChildError> {
///     Ok(x)
/// });
/// assert_eq!(new_result, Ok(()));
///
/// // Case 2: The original result is an Err of type ParentError.
/// let result: Result<(), ParentError> = Err(ParentError::Parent("initial error".to_string()));
/// let new_result: Result<(), ParentError> = result.and_then_map_err(|x| -> Result<(), ChildError> {
///     Ok(x)
/// });
/// assert_eq!(new_result, Err(ParentError::Parent("initial error".to_string())));
/// assert_eq!(new_result.unwrap_err().to_string(), "parent error: initial error");
///
/// // Case 3: The original result is Ok but the operation returns an Err of type ChildError.
/// let result: Result<(), ParentError> = Ok(());
/// let new_result: Result<(), ParentError> = result.and_then_map_err(|x| {
///     Err(ChildError::Child("error occurred afterwards".to_string()))
/// });
/// assert_eq!(new_result, Err(ParentError::FromChild(ChildError::Child("error occurred afterwards".to_string()))));
/// ```
pub trait AndThenMapErr<T, E1> {
    fn and_then_map_err<U, E2, F>(self, op: F) -> Result<U, E1>
    where
        E1: From<E2>,
        F: FnOnce(T) -> Result<U, E2>;
}

impl<T, E1> AndThenMapErr<T, E1> for Result<T, E1> {
    fn and_then_map_err<U, E2, F>(self, op: F) -> Result<U, E1>
    where
        E1: From<E2>,
        F: FnOnce(T) -> Result<U, E2>,
    {
        match self {
            Ok(t) => match op(t) {
                Ok(u) => Ok(u),
                Err(e2) => Err(E1::from(e2)),
            },
            Err(e1) => Err(e1),
        }
    }
}

/// The `map_err_and_then` trait allows for error mapping on `Result` types.
/// This trait converts an error in the initial `Result<T, E1>` to a different error type `E2`
/// if the operation fails.
///
/// # Examples
///
/// ```
/// use thiserror::Error;
/// use and_then_map_err::MapErrAndThen;
///
/// #[derive(Error, Debug, Eq, PartialEq)]
/// pub enum ParentError {
///     #[error("parent error: {0}")]
///     Parent(String),
///     #[error("parent error from child error: {0}")]
///     FromChild(#[from] ChildError),
/// }
///
/// #[derive(Error, Debug, Eq, PartialEq)]
/// pub enum ChildError {
///     #[error("child error: {0}")]
///     Child(String),
/// }
///
/// // Case 1: The original result is Ok and the operation succeeds.
/// let result: Result<(), ChildError> = Ok(());
/// let new_result: Result<(), ParentError> = result.map_err_and_then(|x| {
///     Ok(x)
/// });
/// assert_eq!(new_result, Ok(()));
///
/// // Case 2: The original result is an Err of type ChildError.
/// let result: Result<(), ChildError> = Err(ChildError::Child("initial error".to_string()));
/// let new_result: Result<(), ParentError> = result.map_err_and_then(|x| {
///     Ok(x)
/// });
/// assert_eq!(new_result, Err(ParentError::FromChild(ChildError::Child("initial error".to_string()))));
/// assert_eq!(new_result.unwrap_err().to_string(), "parent error from child error: child error: initial error");
///
/// // Case 3: The original result is Ok but the operation returns an Err of type ParentError.
/// let result: Result<(), ChildError> = Ok(());
/// let new_result: Result<(), ParentError> = result.map_err_and_then(|x| {
///     Err(ParentError::Parent("error occurred afterwards".to_string()))
/// });
/// assert_eq!(new_result, Err(ParentError::Parent("error occurred afterwards".to_string())));
/// assert_eq!(new_result.unwrap_err().to_string(), "parent error: error occurred afterwards");
/// ```
pub trait MapErrAndThen<T, E1> {
    fn map_err_and_then<U, E2, F>(self, op: F) -> Result<U, E2>
    where
        E2: From<E1>,
        F: FnOnce(T) -> Result<U, E2>;
}

impl<T, E1> MapErrAndThen<T, E1> for Result<T, E1> {
    fn map_err_and_then<U, E2, F>(self, op: F) -> Result<U, E2>
    where
        E2: From<E1>,
        F: FnOnce(T) -> Result<U, E2>,
    {
        match self {
            Ok(t) => match op(t) {
                Ok(u) => Ok(u),
                Err(e2) => Err(e2),
            },
            Err(e1) => Err(E2::from(e1)),
        }
    }
}

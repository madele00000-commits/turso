//! Which casts PostgreSQL has between its types, and how they convert a value.
//!
//! `CASTS` lists the casts of `pg_cast`. A cast to text goes through the
//! output function of the source type, and a cast from text through the input
//! function of the target type, as in PostgreSQL. Any other pair of types is
//! refused with SQLSTATE 42846.

use crate::error::sqlstate_error;
use crate::functions::{parse_pg_bool, validate_pg_input};
use turso_core::ast;
use turso_core::dialect::{AppliedCast, CastContext, CastSource};
use turso_core::{LimboError, Numeric, Register, Result, Value};
use turso_pg_parser::sqlstate::{
    SQLSTATE_CANNOT_COERCE, SQLSTATE_DATATYPE_MISMATCH, SQLSTATE_INVALID_TEXT_REPRESENTATION,
    SQLSTATE_NUMERIC_VALUE_OUT_OF_RANGE,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CastType {
    Int2,
    Int4,
    Int8,
    Float4,
    Float8,
    Numeric,
    Text,
    Bool,
    // FIXME(pg-catalog): bytea is not a registered type yet, so its casts stay with the engine. The commented bytea lines in this file come back with the pg_type row of bytea.
    // Bytea,
    Timestamp,
    TimestampTz,
}

impl CastType {
    fn name(self) -> &'static str {
        match self {
            Self::Int2 => "int2",
            Self::Int4 => "int4",
            Self::Int8 => "int8",
            Self::Float4 => "float4",
            Self::Float8 => "float8",
            Self::Numeric => "numeric",
            Self::Text => "text",
            Self::Bool => "bool",
            // Self::Bytea => "bytea",
            Self::Timestamp => "timestamp",
            Self::TimestampTz => "timestamptz",
        }
    }

    pub(crate) fn oid(self) -> i64 {
        crate::catalog::pg_type_oid(self.name()).expect("every cast type has a pg_type oid")
    }

    fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "int2" | "smallint" => Self::Int2,
            "int4" => Self::Int4,
            "int8" | "bigint" => Self::Int8,
            "float4" => Self::Float4,
            "float8" => Self::Float8,
            "numeric" => Self::Numeric,
            "text" | "varchar" => Self::Text,
            "bool" | "boolean" => Self::Bool,
            // "bytea" => Self::Bytea,
            "timestamp" => Self::Timestamp,
            "timestamptz" => Self::TimestampTz,
            _ => return None,
        })
    }

    /// FIXME(pg-catalog): This hand-codes which PostgreSQL type a column has from the SQLite type name the schema keeps, so an int4 or float4 column is only checked for the range of int8 or float8. The atttypid of the column in pg_attribute, looked up in pg_type, replaces this.
    /// The type of a column, which the schema keeps by its SQLite type name.
    fn from_column_type(name: &str) -> Option<Self> {
        match name {
            "integer" => Some(Self::Int8),
            "real" => Some(Self::Float8),
            _ => Self::from_name(name),
        }
    }

    fn is_integer(self) -> bool {
        matches!(self, Self::Int2 | Self::Int4 | Self::Int8)
    }

    fn is_float(self) -> bool {
        matches!(self, Self::Float4 | Self::Float8)
    }
}

struct Cast {
    source: CastType,
    target: CastType,
    context: CastContext,
}

const fn cast(source: CastType, target: CastType, context: CastContext) -> Cast {
    Cast {
        source,
        target,
        context,
    }
}

use CastContext::{Assignment as A, Explicit as E, Implicit as I};
use CastType::*;

const CASTS: &[Cast] = &[
    cast(Int2, Int4, I),
    cast(Int2, Int8, I),
    cast(Int4, Int8, I),
    cast(Int4, Int2, A),
    cast(Int8, Int2, A),
    cast(Int8, Int4, A),
    cast(Int2, Float4, I),
    cast(Int4, Float4, I),
    cast(Int8, Float4, I),
    cast(Int2, Float8, I),
    cast(Int4, Float8, I),
    cast(Int8, Float8, I),
    cast(Int2, Numeric, I),
    cast(Int4, Numeric, I),
    cast(Int8, Numeric, I),
    // cast(Int2, Bytea, E),
    // cast(Int4, Bytea, E),
    // cast(Int8, Bytea, E),
    // cast(Bytea, Int2, E),
    // cast(Bytea, Int4, E),
    // cast(Bytea, Int8, E),
    cast(Int4, Bool, E),
    cast(Bool, Int4, E),
    cast(Float4, Float8, I),
    cast(Float8, Float4, A),
    cast(Float4, Int2, A),
    cast(Float4, Int4, A),
    cast(Float4, Int8, A),
    cast(Float8, Int2, A),
    cast(Float8, Int4, A),
    cast(Float8, Int8, A),
    cast(Float4, Numeric, A),
    cast(Float8, Numeric, A),
    cast(Numeric, Int2, A),
    cast(Numeric, Int4, A),
    cast(Numeric, Int8, A),
    cast(Numeric, Float4, I),
    cast(Numeric, Float8, I),
    cast(Timestamp, TimestampTz, I),
    cast(TimestampTz, Timestamp, A),
];

/// The `oid` of the first row of `pg_cast`.
pub(crate) const FIRST_CAST_OID: i64 = 10_000;

/// The rows of `pg_cast`: source, target, the letter of the context and the
/// letter of the method. A cast from or to text goes through the text input
/// or output function, and the others through a conversion function.
pub(crate) fn cast_rows() -> impl Iterator<Item = (CastType, CastType, &'static str, &'static str)>
{
    CASTS.iter().map(|cast| {
        let context = match cast.context {
            CastContext::Implicit => "i",
            CastContext::Assignment => "a",
            CastContext::Explicit => "e",
        };
        let method = if cast.source == Text || cast.target == Text {
            "i"
        } else {
            "f"
        };
        (cast.source, cast.target, context, method)
    })
}

enum Resolution {
    Unchanged,
    Convert,
}

fn resolve(source: CastType, target: CastType, context: CastContext) -> Result<Resolution> {
    if source == target {
        return Ok(Resolution::Unchanged);
    }
    let listed = CASTS
        .iter()
        .any(|cast| cast.source == source && cast.target == target && cast.context <= context);
    let through_text = (target == Text && context >= CastContext::Assignment)
        || (source == Text && context == CastContext::Explicit);
    if listed || through_text {
        return Ok(Resolution::Convert);
    }
    let (sqlstate, message) = match context {
        CastContext::Assignment => (
            SQLSTATE_DATATYPE_MISMATCH,
            format!(
                "a value of type {} cannot be assigned to type {}",
                source.name(),
                target.name()
            ),
        ),
        _ => (
            SQLSTATE_CANNOT_COERCE,
            format!("cannot cast type {} to {}", source.name(), target.name()),
        ),
    };
    Err(sqlstate_error(sqlstate, message, None))
}

/// The cast PostgreSQL does for a CAST of `operand` to `target`, or None for a
/// cast the engine does as it did before: a source or target type that
/// `CastType` does not list.
pub(crate) fn apply_cast(
    operand: &ast::Expr,
    source: &dyn Fn() -> CastSource,
    target: &ast::Type,
    context: CastContext,
) -> Result<Option<AppliedCast>> {
    if target.array_dimensions > 0 {
        return Ok(None);
    }
    let target_name = target.name.to_ascii_lowercase();
    let target_type = match context {
        CastContext::Assignment => CastType::from_column_type(&target_name),
        _ => CastType::from_name(&target_name),
    };
    let Some(target_type) = target_type else {
        return Ok(None);
    };
    let (source_type, context) = match source() {
        CastSource::Untyped => (Text, CastContext::Explicit),
        CastSource::Typed(source) => match source_type(&source) {
            Some(source_type) => (source_type, context),
            None => return Ok(None),
        },
        CastSource::Unnamed => return Ok(None),
    };
    let operand = match resolve(source_type, target_type, context)? {
        Resolution::Convert if needs_conversion(source_type, target_type) => {
            conversion_call(operand, source_type, target_type)
        }
        _ => operand.clone(),
    };
    Ok(Some(AppliedCast {
        operand,
        target: target.clone(),
    }))
}

fn conversion_call(operand: &ast::Expr, source: CastType, target: CastType) -> ast::Expr {
    let name = |name: &str| ast::Expr::Literal(ast::Literal::String(format!("'{name}'")));
    let args = [operand.clone(), name(source.name()), name(target.name())]
        .into_iter()
        .map(Box::new)
        .collect();
    ast::Expr::FunctionCall {
        name: ast::Name::exact("pg_cast".to_string()),
        distinctness: None,
        args,
        order_by: vec![],
        within_group: vec![],
        filter_over: ast::FunctionTail {
            filter_clause: None,
            over_clause: None,
        },
    }
}

/// FIXME(pg-catalog): This hand-codes the PostgreSQL type of a value from the SQLite type name the engine gives an expression (an integer literal or sum is int4, a float is float8). The result type of the operator or function in pg_operator and pg_proc, and the type oid in pg_type, replace this.
fn source_type(source: &ast::Type) -> Option<CastType> {
    if source.array_dimensions > 0 {
        return None;
    }
    match source.name.to_ascii_lowercase().as_str() {
        "integer" => Some(Int4),
        "real" => Some(Float8),
        "numeric" => Some(Numeric),
        "text" => Some(Text),
        // "blob" => Some(Bytea),
        name => CastType::from_name(name),
    }
}

/// Whether the engine's own store of the value as the target type gives the
/// right value, which makes the conversion function unnecessary: the type
/// checks and encodes a value that is text.
fn needs_conversion(source: CastType, target: CastType) -> bool {
    !matches!(
        (source, target),
        // (Text, Bytea)
        (Text, Timestamp | TimestampTz) | (Timestamp | TimestampTz, Timestamp | TimestampTz)
    )
}

/// `pg_cast(value, source, target)`: the value converted from the type named
/// `source` to the type named `target`.
pub(crate) fn exec_pg_cast(args: &[Register]) -> Result<Value> {
    let value = args[0].get_value();
    let (Some(source), Some(target)) = (type_arg(&args[1]), type_arg(&args[2])) else {
        return Err(LimboError::InternalError(
            "pg_cast needs the names of two types".to_string(),
        ));
    };
    if matches!(value, Value::Null) {
        return Ok(Value::Null);
    }
    convert(value, source, target)
}

fn type_arg(arg: &Register) -> Option<CastType> {
    match arg.get_value() {
        Value::Text(name) => CastType::from_name(name.as_str()),
        _ => None,
    }
}

fn convert(value: &Value, source: CastType, target: CastType) -> Result<Value> {
    if target.is_integer() {
        return to_integer(value, source, target);
    }
    if target.is_float() {
        return to_float(value, source, target);
    }
    match target {
        // Bytea => integer_to_bytea(value, source),
        Text => to_text(value, source),
        Bool => to_bool(value),
        _ => Ok(value.clone()),
    }
}

fn to_integer(value: &Value, source: CastType, target: CastType) -> Result<Value> {
    let number = match (value, source) {
        (Value::Text(text), CastType::Numeric) => {
            numeric_to_i64(parse_numeric(text.as_str())?.round(), target)?
        }
        (Value::Text(text), _) => {
            return parse_integer(text.as_str(), target).map(Value::from_i64);
        }
        (Value::Numeric(Numeric::Integer(n)), _) => *n,
        // (Value::Blob(bytes), _) => bytea_to_integer(bytes, target)?,
        (Value::Numeric(Numeric::Float(f)), CastType::Numeric) => {
            numeric_to_i64(f64::from(*f).round(), target)?
        }
        (Value::Numeric(Numeric::Float(f)), _) => {
            float_to_i64(f64::from(*f).round_ties_even(), target)?
        }
        _ => return Ok(value.clone()),
    };
    check_integer_range(number, target)?;
    Ok(Value::from_i64(number))
}

fn to_bool(value: &Value) -> Result<Value> {
    match value {
        Value::Numeric(Numeric::Integer(n)) => Ok(Value::from_i64((*n != 0) as i64)),
        Value::Text(text) => match parse_pg_bool(text.as_str()) {
            Some(truth) => Ok(Value::from_i64(truth as i64)),
            None => Err(input_error(text.as_str(), "boolean")),
        },
        _ => Ok(value.clone()),
    }
}

// fn bytea_to_integer(bytes: &[u8], target: CastType) -> Result<i64> {
//     let width = match target {
//         Int2 => 2,
//         Int4 => 4,
//         _ => 8,
//     };
//     if bytes.len() > width {
//         return Err(out_of_range(target));
//     }
//     let negative = bytes.len() == width && bytes[0] & 0x80 != 0;
//     let mut number: i64 = if negative { -1 } else { 0 };
//     for byte in bytes {
//         number = (number << 8) | i64::from(*byte);
//     }
//     Ok(number)
// }
//
// fn integer_to_bytea(value: &Value, source: CastType) -> Result<Value> {
//     let Some(number) = value.as_int() else {
//         return Ok(value.clone());
//     };
//     let width = match source {
//         Int2 => 2,
//         Int4 => 4,
//         _ => 8,
//     };
//     let bytes = &number.to_be_bytes()[8 - width..];
//     let blob = turso_core::types::value_blob_from_slice(bytes)
//         .map_err(|_| LimboError::InternalError("out of memory".to_string()))?;
//     Ok(Value::from_blob(blob))
// }

/// A decimal literal just below 2^63 reads as 2^63. The translator has refused
/// the literals that are out of range, so this one is the largest bigint.
fn numeric_to_i64(rounded: f64, target: CastType) -> Result<i64> {
    if rounded == 9223372036854775808.0 {
        return Ok(i64::MAX);
    }
    float_to_i64(rounded, target)
}

fn float_to_i64(rounded: f64, target: CastType) -> Result<i64> {
    // 2^63 is not an i64, and every float at or past it is out of range.
    if !(-9223372036854775808.0..9223372036854775808.0).contains(&rounded) {
        return Err(out_of_range(target));
    }
    Ok(rounded as i64)
}

fn check_integer_range(number: i64, target: CastType) -> Result<()> {
    let fits = match target {
        Int2 => i16::try_from(number).is_ok(),
        Int4 => i32::try_from(number).is_ok(),
        _ => true,
    };
    if fits {
        Ok(())
    } else {
        Err(out_of_range(target))
    }
}

fn out_of_range(target: CastType) -> LimboError {
    let message = match target {
        Int2 => "smallint out of range",
        Int4 => "integer out of range",
        _ => "bigint out of range",
    };
    sqlstate_error(SQLSTATE_NUMERIC_VALUE_OUT_OF_RANGE, message, None)
}

fn parse_integer(text: &str, target: CastType) -> Result<i64> {
    let type_name = target.name();
    if let Some((message, code)) = validate_pg_input(text, type_name) {
        return Err(sqlstate_error(sqlstate_of(&code), message, None));
    }
    text.trim()
        .parse::<i64>()
        .map_err(|_| input_error(text, "integer"))
}

fn sqlstate_of(code: &str) -> &'static str {
    if code == SQLSTATE_NUMERIC_VALUE_OUT_OF_RANGE {
        SQLSTATE_NUMERIC_VALUE_OUT_OF_RANGE
    } else {
        SQLSTATE_INVALID_TEXT_REPRESENTATION
    }
}

fn input_error(text: &str, type_name: &str) -> LimboError {
    sqlstate_error(
        SQLSTATE_INVALID_TEXT_REPRESENTATION,
        format!("invalid input syntax for type {type_name}: \"{text}\""),
        None,
    )
}

fn to_float(value: &Value, source: CastType, target: CastType) -> Result<Value> {
    let number = match value {
        Value::Numeric(Numeric::Integer(n)) => *n as f64,
        Value::Numeric(Numeric::Float(f)) => f64::from(*f),
        Value::Text(text) if source == CastType::Numeric => parse_numeric(text.as_str())?,
        Value::Text(text) => parse_float(text.as_str(), target)?,
        _ => return Ok(value.clone()),
    };
    if target == Float4 {
        let narrowed = number as f32;
        if narrowed.is_infinite() && number.is_finite() {
            return Err(sqlstate_error(
                SQLSTATE_NUMERIC_VALUE_OUT_OF_RANGE,
                "value out of range: overflow",
                None,
            ));
        }
        if narrowed == 0.0 && number != 0.0 {
            return Err(sqlstate_error(
                SQLSTATE_NUMERIC_VALUE_OUT_OF_RANGE,
                "value out of range: underflow",
                None,
            ));
        }
        return Ok(Value::from_f64(shortest_float8(narrowed)));
    }
    Ok(Value::from_f64(number))
}

/// The float8 that prints with the digits of the float4, so 0.1 as a float4
/// stays 0.1 and is not 0.10000000149011612.
fn shortest_float8(narrowed: f32) -> f64 {
    narrowed
        .to_string()
        .parse()
        .unwrap_or_else(|_| f64::from(narrowed))
}

/// A numeric with a type modifier is stored as its text.
fn parse_numeric(text: &str) -> Result<f64> {
    text.trim()
        .parse()
        .map_err(|_| input_error(text, "numeric"))
}

fn parse_float(text: &str, target: CastType) -> Result<f64> {
    let trimmed = text.trim();
    let lowered = trimmed.to_ascii_lowercase();
    match lowered.as_str() {
        "nan" => return Ok(f64::NAN),
        "infinity" | "inf" | "+infinity" | "+inf" => return Ok(f64::INFINITY),
        "-infinity" | "-inf" => return Ok(f64::NEG_INFINITY),
        _ => {}
    }
    let type_name = if target == Float4 {
        "real"
    } else {
        "double precision"
    };
    let invalid = trimmed.is_empty()
        || trimmed
            .chars()
            .any(|c| !(c.is_ascii_digit() || matches!(c, '.' | 'e' | 'E' | '+' | '-')));
    match trimmed.parse::<f64>() {
        Ok(number) if !invalid && number.is_infinite() => Err(sqlstate_error(
            SQLSTATE_NUMERIC_VALUE_OUT_OF_RANGE,
            format!("\"{text}\" is out of range for type {type_name}"),
            None,
        )),
        Ok(number) if !invalid => Ok(number),
        _ => Err(input_error(text, type_name)),
    }
}

fn to_text(value: &Value, source: CastType) -> Result<Value> {
    let text = match (value, source) {
        (Value::Numeric(Numeric::Integer(n)), CastType::Bool) => {
            if *n == 0 { "false" } else { "true" }.to_string()
        }
        (Value::Numeric(Numeric::Integer(n)), _) => n.to_string(),
        // (Value::Blob(bytes), _) => crate::text::pgwire_text::encode_bytea(bytes, false),
        _ => return Ok(value.clone()),
    };
    Ok(Value::build_text(text))
}

//! Format numbers with delimiters, but without allocations or even the standard
//! library itself, `#![no_std]` mode one!
//!
//! ```rust
//! use num_fmt_delimited::{two, three, four};
//! // Group by two digits:
//! assert_eq!(two::with_space(12345).to_string(), "1 23 45");
//! assert_eq!(two::with_space(-12345).to_string(), "-1 23 45");
//! // Or by three:
//! assert_eq!(three::with_space(12345).to_string(), "12 345");
//! assert_eq!(three::with_space(-12345).to_string(), "-12 345");
//! // Or by four!
//! assert_eq!(four::with_space(12345).to_string(), "1 2345");
//! assert_eq!(four::with_space(-12345).to_string(), "-1 2345");
//! // Custom delimiters supported:
//! assert_eq!(two::with_delimiter(12345, ',').to_string(), "1,23,45");
//! assert_eq!(two::with_delimiter(12345, ",").to_string(), "1,23,45");
//! assert_eq!(two::with_delimiter(12345, "-_-").to_string(), "1-_-23-_-45");
//! assert_eq!(two::with_delimiter(12345, "-_-").to_string(), "1-_-23-_-45");
//! ```
//!
//! While marker types for groups of 2, 3 and 4 digits are pre-implemented
//! ([Two], [Three] and [Four] respectively), you can always go with your own
//! number of digits to group by:
//!
//! ```rust
//! use num_fmt_delimited::{FixedLength, FormatWithDelimiter};
//! struct Eight;
//! impl FixedLength for Eight {
//!     // As simple and straightforward as that.
//!     const LENGTH: u32 = 8;
//! }
//!
//! /// A helper function to group digits by eight!
//! fn eight<Number>(number: Number) -> FormatWithDelimiter<Number, char, Eight> {
//!     FormatWithDelimiter::<_, _, Eight>::with_length(number)
//! }
//! // And it will automagically work.
//! assert_eq!(eight(1234567890).to_string(), "12 34567890");
//! ```

#![no_std]
#![deny(missing_docs)]

#[cfg(test)]
extern crate alloc;

use core::{fmt, marker::PhantomData};

macro_rules! make_module {
    (
        $($mod_name:ident: $ty:ident, $lit_singular:literal, $lit_plural:literal, $length:literal),*
        $(,)?
    ) => {
        $(make_module!(@one $mod_name: $ty, $lit_singular, $lit_plural, $length);)*
    };
    (@one
        $mod_name:ident: $ty:ident, $lit_singular:literal, $lit_plural:literal, $length:literal
    ) => {
        #[doc = "A maker type for separating numbers in groups of"]
        #[doc = $lit_singular]
        #[doc = "digits."]
        pub struct $ty;

        impl FixedLength for $ty {
            const LENGTH: u32 = $length;
        }

        pub mod $mod_name {
            // We use multiple `doc` attributes (here and later) in order to put
            // the whole sentence to the doc's preview. Otherwise only the first
            // line will go there.
            #![doc = "A convenience module that contains a formatter which groups digits in"]
            #![doc = $lit_plural]
            #![doc = "using various delimiters."]

            use super::*;

            #[doc = "Creates a formatter which groups digits in"]
            #[doc = $lit_plural]
            #[doc = "using spaces."]
            ///
            /// See [crate] documentation for examples.
            pub fn with_space<Number>(number: Number) -> FormatWithDelimiter<Number, char, $ty> {
                FormatWithDelimiter::with_length(number)
            }

            #[doc = "Creates a formatter which groups digits in"]
            #[doc = $lit_plural]
            #[doc = "using custom delimiter."]
            ///
            /// See [crate] documentation for examples.
            pub fn with_delimiter<Number, Delimiter>(
                number: Number, delimiter: Delimiter
            ) -> FormatWithDelimiter<Number, Delimiter, $ty> {
                FormatWithDelimiter::with_delimiter_and_length(number, delimiter)
            }
        }
    };
}

#[rustfmt::skip]
make_module!(
    two: Two, "two", "twos", 2,
    three: Three, "three", "threes", 3,
    four: Four, "four", "fours", 4,
);

/// A helper type that implements [Debug][fmt::Debug] and
/// [Display][fmt::Display] traits which splits long numbers with some
/// delimiter.
///
/// There are certain type bounds which are required to be satisfied in order
/// for the type to implement formatting traits:
/// 1. `Number` must be [Copy] and implement [Divisible] trait.
/// 2. If you want [Display][fmt::Display] implementation, `Number` must also
///    implement it.
/// 3. If you want [Debug][fmt::Debug] implementation, `Number` must also
///    implement it.
/// 4. `Delimiter` must implement [Display][fmt::Display] and be [Clone]-able.
/// 5. `Length` must implement [FixedLength].
///
/// The first three items are automatically satisfied when you use rust built-in
/// integers ([u8]/[i64]/etc.), but if you want the formatter to work for other
/// types, please consider implementing the aforementioned traits for them.
///
/// # Note on 128-bit integers support.
///
/// Implementation of the [Divisible] trait for `u128`/`i128` types is only
/// activated with the `128bit` feature (which is on by default), which gives
/// you a possibility to opt-out of the implementations by using the crate
/// without default features.
#[derive(Clone, Copy)]
pub struct FormatWithDelimiter<Number, Delimiter = char, Length = Three> {
    number: Number,
    delimiter: Delimiter,
    _pd: PhantomData<Length>,
}

impl<Number> FormatWithDelimiter<Number, char> {
    /// Creates a helper that format the number with spaces, splitting the
    /// number in groups of three digits.
    pub fn new(number: Number) -> Self {
        Self::with_delimiter(number, ' ')
    }
}

impl<Number, Delimiter> FormatWithDelimiter<Number, Delimiter> {
    /// Creates a helper that formats the number with the given delimiter.
    pub fn with_delimiter(number: Number, delimiter: Delimiter) -> Self {
        Self::with_delimiter_and_length(number, delimiter)
    }
}

impl<Number, Length> FormatWithDelimiter<Number, char, Length> {
    /// Creates a helper that formats the number with spaces, splitting the
    /// number in groups of the specified length.
    pub fn with_length(number: Number) -> Self {
        Self::with_delimiter_and_length(number, ' ')
    }
}

impl<Number, Delimiter, Length> FormatWithDelimiter<Number, Delimiter, Length> {
    /// Creates a helper that formats the number with the given delimiter.
    pub fn with_delimiter_and_length(number: Number, delimiter: Delimiter) -> Self {
        FormatWithDelimiter {
            number,
            delimiter,
            _pd: PhantomData,
        }
    }
}

macro_rules! impl_trait {
    ($trait:path, $dbg_fmt:literal) => {
        impl<Number, Delimiter, Length> $trait for FormatWithDelimiter<Number, Delimiter, Length>
        where
            Number: Divisible<Length> + Copy,
            Length: FixedLength,
            Number: $trait,
            Delimiter: fmt::Display + Clone,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let (quotient, remainder) = self.number.divide();
                if quotient.is_zero() {
                    // Formatting string is either
                    //   "{:?}"
                    // or
                    //   "{:}"
                    write!(f, concat!("{:", $dbg_fmt, "}"), remainder)?;
                } else {
                    <Self as $trait>::fmt(
                        &FormatWithDelimiter {
                            number: quotient,
                            delimiter: self.delimiter.clone(),
                            _pd: PhantomData,
                        },
                        f,
                    )?;
                    // Formatting string is either
                    //   "{delimiter:0}{remainder:00$?}"
                    // or
                    //   "{delimiter:0}{remainder:00$}"
                    write!(
                        f,
                        concat!("{delimiter:0}{remainder:00$", $dbg_fmt, "}"),
                        Length::LENGTH as usize,
                        delimiter = self.delimiter,
                        remainder = remainder.into_positive(),
                    )?;
                }
                Ok(())
            }
        }
    };
}

impl_trait!(fmt::Debug, "?");
impl_trait!(fmt::Display, "");

/// A helper trait to evade not-yet-stabilized const generics.
pub trait FixedLength {
    /// Well.. the length!
    const LENGTH: u32;
}

/// A helper trait to split long numbers, like `12345` -> `(12, 345)`.
pub trait Divisible<Length: FixedLength>: Copy {
    /// Returns *quotient* and *remainder* when `self` is divided by 10^Length.
    fn divide(self) -> (Self, Self)
    where
        Self: Sized;

    /// Returns `true` if `self == 0`.
    fn is_zero(self) -> bool;

    /// Returns `true` if `self < 0`.
    fn is_negative(self) -> bool;

    /// Converts `self` into its positive counterpart.
    fn into_positive(self) -> Self
    where
        Self: Sized;
}

macro_rules! implement_divisible_unsigned {
    ($($type:ty),+ $(,)?) => {
        $(
            impl<Length: FixedLength> Divisible<Length> for $type {
                fn divide(self) -> (Self, Self)
                where
                    Self: Sized,
                {
                    let divisor: $type = match (10 as $type).checked_pow(Length::LENGTH) {
                        Some(x) => x,
                        None => return (0 as $type, self),
                    };
                    let quotient = self / divisor;
                    let remainder = self % divisor;
                    (quotient, remainder)
                }

                #[inline(always)]
                fn is_zero(self) -> bool {
                    self == (0 as $type)
                }

                #[inline(always)]
                fn is_negative(self) -> bool {
                    false
                }

                #[inline(always)]
                fn into_positive(self) -> Self {
                    self
                }
            }
        )*
    };
}

macro_rules! implement_divisible_signed {
    ($($type:ty),+ $(,)?) => {
        $(
            impl<Length: FixedLength> Divisible<Length> for $type {
                fn divide(self) -> (Self, Self)
                where
                    Self: Sized,
                {
                    let divisor: $type = match (10 as $type).checked_pow(Length::LENGTH) {
                        Some(x) => x,
                        None => return (0 as $type, self),
                    };
                    let quotient = self / divisor;
                    let remainder = self % divisor;
                    (quotient, remainder)
                }

                #[inline(always)]
                fn is_zero(self) -> bool {
                    self == (0 as $type)
                }

                #[inline(always)]
                fn is_negative(self) -> bool {
                    self < 0
                }

                #[inline(always)]
                fn into_positive(self) -> Self {
                    self.abs()
                }
            }
        )*
    };
}

implement_divisible_unsigned!(u8, u16, u32, u64, usize);
implement_divisible_signed!(i8, i16, i32, i64, isize);

#[cfg(feature = "128bit")]
implement_divisible_unsigned!(u128);

#[cfg(feature = "128bit")]
implement_divisible_signed!(i128);

#[cfg(test)]
mod tests {
    use super::*;

    use alloc::format;

    #[track_caller]
    fn eq<Number, Delimiter, Length>(
        formatter: FormatWithDelimiter<Number, Delimiter, Length>,
        reference: &str,
    ) where
        Number: fmt::Debug + fmt::Display + Copy,
        Delimiter: fmt::Debug + fmt::Display + Copy,
        Length: FixedLength,
        Number: Divisible<Length>,
    {
        assert_eq!(format!("{:?}", formatter), reference);
        assert_eq!(format!("{}", formatter), reference);
    }

    #[test]
    fn positive_stuff_works() {
        // Test zeroes.
        eq(FormatWithDelimiter::new(0u8), "0");
        eq(FormatWithDelimiter::new(0u16), "0");
        eq(FormatWithDelimiter::new(0u32), "0");
        eq(FormatWithDelimiter::new(0u64), "0");
        eq(FormatWithDelimiter::new(0u128), "0");
        eq(FormatWithDelimiter::new(0usize), "0");

        // Split in twos
        eq(
            FormatWithDelimiter::<_, _, Two>::with_length(12_345u16),
            "1 23 45",
        );

        // In threes. Btw note no leading zeroes!
        eq(FormatWithDelimiter::new(12_345u16), "12 345");
        eq(FormatWithDelimiter::new(12_345u32), "12 345");
        eq(FormatWithDelimiter::new(123_456u32), "123 456");
        // Zero is there.
        eq(FormatWithDelimiter::new(123_056u32), "123 056");

        // In fours!
        eq(
            FormatWithDelimiter::<_, _, Four>::with_length(123_056u32),
            "12 3056",
        );
        // Zeroes are there :)
        eq(
            FormatWithDelimiter::<_, _, Four>::with_length(120_056u32),
            "12 0056",
        );
    }

    #[test]
    fn negative_stuff() {
        // Test -1
        eq(FormatWithDelimiter::new(-1), "-1");

        // Ok, let's split something
        eq(FormatWithDelimiter::new(-12_345i16), "-12 345");
        // Split more, and in 2-digits!!
        eq(
            FormatWithDelimiter::<_, _, Two>::with_length(-123456789i32),
            "-1 23 45 67 89",
        );
    }

    #[test]
    fn signed_but_positive() {
        // Test -1
        eq(FormatWithDelimiter::new(1i8), "1");

        // Ok, let's split something
        eq(FormatWithDelimiter::new(12_345i16), "12 345");
        // Split more, and in 2-digits!!
        eq(
            FormatWithDelimiter::<_, _, Two>::with_length(123456789i32),
            "1 23 45 67 89",
        );
    }
}

//! Idiomatic Rust port of <https://github.com/ibc/h264-profile-level-id> by Iñaki Baz Castillo.
//!
//! Rust utility to process [H264](https://tools.ietf.org/html/rfc6184) `profile-level-id` values based on Google's [libwebrtc](https://chromium.googlesource.com/external/webrtc/+/refs/heads/master/media/base/h264_profile_level_id.h) C++ code.
//!
//! Basic usage example:
//! ```rust
//! use h264_profile_level_id::{Profile, Level, ProfileLevelId};
//!
//! fn main () {
//!     let profile_level_id: ProfileLevelId = "42e01f".parse().unwrap();
//!
//!     assert_eq!(profile_level_id.profile(), Profile::ConstrainedBaseline);
//!     assert_eq!(profile_level_id.level(), Level::Level31);
//!
//!     let s = profile_level_id.to_string();
//!
//!     assert_eq!(s.as_str(), "42e01f");
//!
//!     let local_profile_level_id = "42e01f".parse::<ProfileLevelId>().ok();
//!     let local_level_asymmetry_allowed = true;
//!
//!     let remote_profile_level_id = "42e015".parse::<ProfileLevelId>().ok();
//!     let remote_level_asymmetry_allowed = true;
//!
//!     assert_eq!(
//!         h264_profile_level_id::generate_profile_level_id_for_answer(
//!             local_profile_level_id,
//!             local_level_asymmetry_allowed,
//!             remote_profile_level_id,
//!             remote_level_asymmetry_allowed
//!         ),
//!         Ok("42e01f".parse::<ProfileLevelId>().unwrap()),
//!     );
//! }
//! ```

use bitpattern::bitpattern;
use log::debug;
use std::convert::{TryFrom, TryInto};
use std::str::FromStr;
use thiserror::Error;

// This is from https://tools.ietf.org/html/rfc6184#section-8.1.
const PROFILE_LEVEL_PATTERNS: [ProfilePattern; 8] = [
    ProfilePattern {
        profile_idc: 0x42,
        profile_iop: |input| bitpattern!("?1??0000", input).is_some(),
        profile: Profile::ConstrainedBaseline,
    },
    ProfilePattern {
        profile_idc: 0x4D,
        profile_iop: |input| bitpattern!("1???0000", input).is_some(),
        profile: Profile::ConstrainedBaseline,
    },
    ProfilePattern {
        profile_idc: 0x58,
        profile_iop: |input| bitpattern!("11??0000", input).is_some(),
        profile: Profile::ConstrainedBaseline,
    },
    ProfilePattern {
        profile_idc: 0x42,
        profile_iop: |input| bitpattern!("?0??0000", input).is_some(),
        profile: Profile::Baseline,
    },
    ProfilePattern {
        profile_idc: 0x58,
        profile_iop: |input| bitpattern!("10??0000", input).is_some(),
        profile: Profile::Baseline,
    },
    ProfilePattern {
        profile_idc: 0x4D,
        profile_iop: |input| bitpattern!("0?0?0000", input).is_some(),
        profile: Profile::Main,
    },
    ProfilePattern {
        profile_idc: 0x64,
        profile_iop: |input| bitpattern!("00000000", input).is_some(),
        profile: Profile::High,
    },
    ProfilePattern {
        profile_idc: 0x64,
        profile_iop: |input| bitpattern!("00001100", input).is_some(),
        profile: Profile::ConstrainedHigh,
    },
    ProfilePattern {
        profile_idc: 0xF4,
        profile_iop: |input| bitpattern!("00000000", input).is_some(),
        profile: Profile::PredictiveHigh444,
    },
];

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Profile {
    ConstrainedBaseline = 1,
    Baseline = 2,
    Main = 3,
    ConstrainedHigh = 4,
    High = 5,
    PredictiveHigh444 = 6,
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
// All values are equal to ten times the level number, except level 1b which is special.
pub enum Level {
    /// Level 1b
    Level1b = 0,
    /// Level 1
    Level1 = 10,
    /// Level 1.1
    Level11 = 11,
    /// Level 1.2
    Level12 = 12,
    /// Level 1.3
    Level13 = 13,
    /// Level 2
    Level2 = 20,
    /// Level 2.1
    Level21 = 21,
    /// Level 2.2
    Level22 = 22,
    /// Level 3
    Level3 = 30,
    /// Level 3.1
    Level31 = 31,
    /// Level 3.2
    Level32 = 32,
    /// Level 4
    Level4 = 40,
    /// Level 4.1
    Level41 = 41,
    /// Level 4.2
    Level42 = 42,
    /// Level 5
    Level5 = 50,
    /// Level 5.1
    Level51 = 51,
    /// Level 5.2
    Level52 = 52,
}

impl TryFrom<u8> for Level {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            // Not a thing here
            // 0 => Ok(Self::Level1b),
            10 => Ok(Self::Level1),
            11 => Ok(Self::Level11),
            12 => Ok(Self::Level12),
            13 => Ok(Self::Level13),
            20 => Ok(Self::Level2),
            21 => Ok(Self::Level21),
            22 => Ok(Self::Level22),
            30 => Ok(Self::Level3),
            31 => Ok(Self::Level31),
            32 => Ok(Self::Level32),
            40 => Ok(Self::Level4),
            41 => Ok(Self::Level41),
            42 => Ok(Self::Level42),
            50 => Ok(Self::Level5),
            51 => Ok(Self::Level51),
            52 => Ok(Self::Level52),
            _ => Err(()),
        }
    }
}

// For level_idc=11 and profile_idc=0x42, 0x4D, or 0x58, the constraint set3 flag specifies if
// level 1b or level 1.1 is used.
const CONSTRAINT_SET3_FLAG: u8 = 0x10;

// Class for converting between profile_idc/profile_iop to Profile.
struct ProfilePattern {
    profile_idc: u8,
    profile_iop: fn(u8) -> bool,
    profile: Profile,
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum ParseProfileLevelIdError {
    #[error("Failed to parse string as hexadecimal number")]
    FailedToParseNumber,
    #[error("String should consist of 3 bytes in hexadecimal format, received {0}")]
    WrongLength(usize),
    #[error("Unrecognizable level_idc {0}")]
    UnrecognizableLevel(u8),
    #[error("Unrecognizable profile_idc/profile_iop combination")]
    UnrecognizableCombination,
    #[error("Unrecognizable H264 profile level id")]
    Unrecognizable,
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
// Private fields make sure we don't have to worry about incorrect combinations of profile and level
// that are provided from the outside, keeping only valid invariants
/// A container encapsulating both H264 profile and level as parsed from a `profile-level-id` string
pub struct ProfileLevelId {
    profile: Profile,
    level: Level,
}

impl ProfileLevelId {
    pub const fn profile(&self) -> Profile {
        self.profile
    }

    pub const fn level(&self) -> Level {
        self.level
    }
}

impl Default for ProfileLevelId {
    fn default() -> Self {
        // Default ProfileLevelId.
        //
        // TODO: The default should really be profile Baseline and level 1 according to
        //  the spec: https://tools.ietf.org/html/rfc6184#section-8.1. In order to not
        //  break backwards compatibility with older versions of WebRTC where external
        //  codecs don't have any parameters, use profile ConstrainedBaseline level 3_1
        //  instead. This workaround will only be done in an interim period to allow
        //  external clients to update their code.
        //
        // http://crbug/webrtc/6337.
        Self {
            profile: Profile::ConstrainedBaseline,
            level: Level::Level31,
        }
    }
}

impl FromStr for ProfileLevelId {
    type Err = ParseProfileLevelIdError;

    /// Parse profile level id that is represented as a string of 3 hex bytes.
    fn from_str(str: &str) -> Result<Self, Self::Err> {
        // The string should consist of 3 bytes in hexadecimal format.
        if str.len() != 6 {
            return Err(ParseProfileLevelIdError::WrongLength(str.len()));
        }

        let profile_level_id_numeric = match u32::from_str_radix(str, 16) {
            Ok(profile_level_id_numeric) => profile_level_id_numeric,
            Err(_) => {
                return Err(ParseProfileLevelIdError::FailedToParseNumber);
            }
        };

        if profile_level_id_numeric == 0 {
            return Err(ParseProfileLevelIdError::Unrecognizable);
        }

        // Separate into three bytes.
        let level_idc = (profile_level_id_numeric & 0xFF) as u8;
        let profile_iop = ((profile_level_id_numeric >> 8) & 0xFF) as u8;
        let profile_idc = ((profile_level_id_numeric >> 16) & 0xFF) as u8;

        // Parse level based on level_idc and constraint set 3 flag.
        let level = match level_idc.try_into() {
            Ok(level) => match level {
                Level::Level11 => {
                    if profile_iop & CONSTRAINT_SET3_FLAG != 0 {
                        Level::Level1b
                    } else {
                        Level::Level11
                    }
                }
                level => level,
            },
            _ => {
                return Err(ParseProfileLevelIdError::UnrecognizableLevel(level_idc));
            }
        };

        // Parse profile_idc/profile_iop into a Profile enum.
        for pattern in PROFILE_LEVEL_PATTERNS.iter() {
            if profile_idc == pattern.profile_idc && (pattern.profile_iop)(profile_iop) {
                return Ok(ProfileLevelId {
                    profile: pattern.profile,
                    level,
                });
            }
        }

        Err(ParseProfileLevelIdError::UnrecognizableCombination)
    }
}

impl ToString for ProfileLevelId {
    /// Returns canonical string representation as three hex bytes of the profile level id, or returns
    fn to_string(&self) -> String {
        // Handle special case level == 1b.
        if self.level == Level::Level1b {
            return match self.profile {
                Profile::ConstrainedBaseline => "42f00b".to_string(),
                Profile::Baseline => "42100b".to_string(),
                Profile::Main => "4d100b".to_string(),
                // Level 1b is not allowed for other profiles.
                _ => {
                    // Invalid invariants are impossible to construct outside of this library
                    unreachable!()
                }
            };
        }

        let profile_idc_iop_string = match self.profile {
            Profile::ConstrainedBaseline => "42e0",
            Profile::Baseline => "4200",
            Profile::Main => "4d00",
            Profile::ConstrainedHigh => "640c",
            Profile::High => "6400",
            Profile::PredictiveHigh444 => "f400",
        };

        format!("{}{:02x}", profile_idc_iop_string, self.level as u8)
    }
}

/// Returns `Some` with parsed profiles if string `profile-level-id` correspond to the same H264
/// profile (Baseline, High, etc).
pub fn is_same_profile(
    local_profile_level_id: Option<&str>,
    remote_profile_level_id: Option<&str>,
) -> Option<(ProfileLevelId, ProfileLevelId)> {
    let local_profile_level_id = match local_profile_level_id {
        Some(s) => s.parse::<ProfileLevelId>().ok(),
        None => Some(ProfileLevelId::default()),
    };
    let remote_profile_level_id = match remote_profile_level_id {
        Some(s) => s.parse::<ProfileLevelId>().ok(),
        None => Some(ProfileLevelId::default()),
    };

    // Compare H264 profiles, but not levels.
    if let (Some(local_profile_level_id), Some(remote_profile_level_id)) =
        (local_profile_level_id, remote_profile_level_id)
    {
        if local_profile_level_id.profile == remote_profile_level_id.profile {
            return Some((local_profile_level_id, remote_profile_level_id));
        }
    }

    None
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum GenerateProfileLevelIdForAnswerError {
    #[error("H264 Profile mismatch")]
    ProfileMismatch,
}

/// Generate codec parameters that will be used as answer in an SDP negotiation based on local
/// supported parameters and remote offered parameters. Both `local_profile_level_id` and
/// `remote_profile_level_id` represent sendrecv media descriptions, i.e they are a mix of both
/// encode and decode capabilities. In theory, when the profile in `local_profile_level_id`
/// represent a strict superset of the profile in `remote_profile_level_id`, we could limit the
/// profile in the answer to the profile in `remote_profile_level_id`.
///
/// However, to simplify the code, each supported H264 profile should be listed explicitly in the
/// list of local supported codecs, even if they are redundant. Then each local codec in the list
/// should be tested one at a time against the remote codec, and only when the profiles are equal
/// should this function be called. Therefore, this function does not need to handle profile
/// intersection, and the profile of `local_profile_level_id` and `remote_profile_level_id` must be
/// equal before calling this function. The parameters that are used when negotiating are the level
/// part of `profile-level-id` and `level-asymmetry-allowed`.
///
/// If both `local_profile_level_id` and `remote_profile_level_id` are `None`, default value for
/// [`ProfileLevelId`] will be returned.
pub fn generate_profile_level_id_for_answer(
    local_profile_level_id: Option<ProfileLevelId>,
    local_level_asymmetry_allowed: bool,
    remote_profile_level_id: Option<ProfileLevelId>,
    remote_level_asymmetry_allowed: bool,
) -> Result<ProfileLevelId, GenerateProfileLevelIdForAnswerError> {
    // If both local and remote params do not contain profile-level-id, they are
    // both using the default profile. In this case, don't return anything.
    let (local_profile_level_id, remote_profile_level_id) =
        match (local_profile_level_id, remote_profile_level_id) {
            (None, None) => {
                debug!(
                    "generate_profile_level_id_for_answer() | no profile-level-id in local and \
                    remote params",
                );

                return Ok(ProfileLevelId::default());
            }
            (Some(local_profile_level_id), Some(remote_profile_level_id)) => {
                if local_profile_level_id.profile != remote_profile_level_id.profile {
                    return Err(GenerateProfileLevelIdForAnswerError::ProfileMismatch);
                } else {
                    (local_profile_level_id, remote_profile_level_id)
                }
            }
            _ => return Err(GenerateProfileLevelIdForAnswerError::ProfileMismatch),
        };

    // Parse level information.
    let level_asymmetry_allowed = local_level_asymmetry_allowed && remote_level_asymmetry_allowed;

    let local_level = local_profile_level_id.level;
    let remote_level = remote_profile_level_id.level;
    let min_level = min_level(local_level, remote_level);

    // Determine answer level. When level asymmetry is not allowed, level upgrade
    // is not allowed, i.e., the level in the answer must be equal to or lower
    // than the level in the offer.
    let answer_level = if level_asymmetry_allowed {
        local_level
    } else {
        min_level
    };

    debug!(
        "generate_profile_level_id_for_answer() | result: [profile:{:?}, level:{:?}]",
        local_profile_level_id.profile, answer_level,
    );

    // Return the resulting profile-level-id for the answer parameters.
    Ok(ProfileLevelId {
        profile: local_profile_level_id.profile,
        level: answer_level,
    })
}

// Compare H264 levels and handle the level 1b case.
fn is_less_level(a: Level, b: Level) -> bool {
    if a == Level::Level1b {
        b != Level::Level1 && b != Level::Level1b
    } else if b == Level::Level1b {
        a != Level::Level1
    } else {
        a < b
    }
}

fn min_level(a: Level, b: Level) -> Level {
    if is_less_level(a, b) {
        a
    } else {
        b
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parsing_invalid() {
        // Malformed strings.
        assert_eq!("".parse::<ProfileLevelId>().is_ok(), false);
        assert_eq!(" 42e01f".parse::<ProfileLevelId>().is_ok(), false);
        assert_eq!("4242e01f".parse::<ProfileLevelId>().is_ok(), false);
        assert_eq!("e01f".parse::<ProfileLevelId>().is_ok(), false);
        assert_eq!("gggggg".parse::<ProfileLevelId>().is_ok(), false);

        // Invalid level.
        assert_eq!("42e000".parse::<ProfileLevelId>().is_ok(), false);
        assert_eq!("42e00f".parse::<ProfileLevelId>().is_ok(), false);
        assert_eq!("42e0ff".parse::<ProfileLevelId>().is_ok(), false);

        // Invalid profile.
        assert_eq!("42e11f".parse::<ProfileLevelId>().is_ok(), false);
        assert_eq!("58601f".parse::<ProfileLevelId>().is_ok(), false);
        assert_eq!("64e01f".parse::<ProfileLevelId>().is_ok(), false);
    }

    #[test]
    fn parsing_level() {
        assert_eq!(
            "42e01f".parse::<ProfileLevelId>().unwrap().level,
            Level::Level31,
        );
        assert_eq!(
            "42e00b".parse::<ProfileLevelId>().unwrap().level,
            Level::Level11,
        );
        assert_eq!(
            "42f00b".parse::<ProfileLevelId>().unwrap().level,
            Level::Level1b,
        );
        assert_eq!(
            "42C02A".parse::<ProfileLevelId>().unwrap().level,
            Level::Level42,
        );
        assert_eq!(
            "640c34".parse::<ProfileLevelId>().unwrap().level,
            Level::Level52,
        );
    }

    #[test]
    fn parsed_constrained_baseline() {
        assert_eq!(
            "42e01f".parse::<ProfileLevelId>().unwrap().profile,
            Profile::ConstrainedBaseline,
        );
        assert_eq!(
            "42C02A".parse::<ProfileLevelId>().unwrap().profile,
            Profile::ConstrainedBaseline,
        );
        assert_eq!(
            "4de01f".parse::<ProfileLevelId>().unwrap().profile,
            Profile::ConstrainedBaseline,
        );
        assert_eq!(
            "58f01f".parse::<ProfileLevelId>().unwrap().profile,
            Profile::ConstrainedBaseline,
        );
    }

    #[test]
    fn parsing_baseline() {
        assert_eq!(
            "42a01f".parse::<ProfileLevelId>().unwrap().profile,
            Profile::Baseline,
        );
        assert_eq!(
            "58A01F".parse::<ProfileLevelId>().unwrap().profile,
            Profile::Baseline,
        );
    }

    #[test]
    fn parsing_main() {
        assert_eq!(
            "4D401f".parse::<ProfileLevelId>().unwrap().profile,
            Profile::Main,
        );
    }

    #[test]
    fn parsing_high() {
        assert_eq!(
            "64001f".parse::<ProfileLevelId>().unwrap().profile,
            Profile::High,
        );
    }

    #[test]
    fn parsing_constrained_high() {
        assert_eq!(
            "640c1f".parse::<ProfileLevelId>().unwrap().profile,
            Profile::ConstrainedHigh,
        );
    }

    #[test]
    fn to_string() {
        assert_eq!(
            ProfileLevelId {
                profile: Profile::ConstrainedBaseline,
                level: Level::Level31
            }
            .to_string()
            .as_str(),
            "42e01f",
        );
        assert_eq!(
            ProfileLevelId {
                profile: Profile::Baseline,
                level: Level::Level1
            }
            .to_string()
            .as_str(),
            "42000a",
        );
        assert_eq!(
            ProfileLevelId {
                profile: Profile::Main,
                level: Level::Level31
            }
            .to_string()
            .as_str(),
            "4d001f",
        );
        assert_eq!(
            ProfileLevelId {
                profile: Profile::ConstrainedHigh,
                level: Level::Level42
            }
            .to_string()
            .as_str(),
            "640c2a",
        );
        assert_eq!(
            ProfileLevelId {
                profile: Profile::High,
                level: Level::Level42
            }
            .to_string()
            .as_str(),
            "64002a",
        );
    }

    #[test]
    fn to_string_level_1b() {
        assert_eq!(
            ProfileLevelId {
                profile: Profile::ConstrainedBaseline,
                level: Level::Level1b
            }
            .to_string()
            .as_str(),
            "42f00b",
        );
        assert_eq!(
            ProfileLevelId {
                profile: Profile::Baseline,
                level: Level::Level1b
            }
            .to_string()
            .as_str(),
            "42100b",
        );
        assert_eq!(
            ProfileLevelId {
                profile: Profile::Main,
                level: Level::Level1b
            }
            .to_string()
            .as_str(),
            "4d100b",
        );

        assert_eq!(
            "42e01f"
                .parse::<ProfileLevelId>()
                .unwrap()
                .to_string()
                .as_str(),
            "42e01f",
        );
        assert_eq!(
            "42E01F"
                .parse::<ProfileLevelId>()
                .unwrap()
                .to_string()
                .as_str(),
            "42e01f",
        );
        assert_eq!(
            "4d100b"
                .parse::<ProfileLevelId>()
                .unwrap()
                .to_string()
                .as_str(),
            "4d100b",
        );
        assert_eq!(
            "4D100B"
                .parse::<ProfileLevelId>()
                .unwrap()
                .to_string()
                .as_str(),
            "4d100b",
        );
        assert_eq!(
            "640c2a"
                .parse::<ProfileLevelId>()
                .unwrap()
                .to_string()
                .as_str(),
            "640c2a",
        );
        assert_eq!(
            "640C2A"
                .parse::<ProfileLevelId>()
                .unwrap()
                .to_string()
                .as_str(),
            "640c2a",
        );
    }

    #[test]
    fn test_is_same_profile() {
        assert!(is_same_profile(None, None).is_some());
        assert!(is_same_profile(Some("42e01f"), Some("42C02A")).is_some());
        assert!(is_same_profile(Some("42a01f"), Some("58A01F")).is_some());
        assert!(is_same_profile(Some("42e01f"), None).is_some());
    }

    #[test]
    fn test_is_not_same_profile() {
        assert!(is_same_profile(None, Some("4d001f")).is_none());
        assert!(is_same_profile(Some("42a01f"), Some("640c1f")).is_none());
        assert!(is_same_profile(Some("42000a"), Some("64002a")).is_none());
    }

    #[test]
    fn generate_profile_level_id_for_answer_empty() {
        assert_eq!(
            generate_profile_level_id_for_answer(None, false, None, false),
            Ok(ProfileLevelId::default()),
        );
    }

    #[test]
    fn generate_profile_level_id_for_answer_level_symmetry_capped() {
        let low_level = "42e015".parse::<ProfileLevelId>().ok();
        let high_level = "42e01f".parse::<ProfileLevelId>().ok();

        assert_eq!(
            generate_profile_level_id_for_answer(low_level, false, high_level, false),
            Ok("42e015".parse::<ProfileLevelId>().unwrap()),
        );
        assert_eq!(
            generate_profile_level_id_for_answer(high_level, false, low_level, false),
            Ok("42e015".parse::<ProfileLevelId>().unwrap()),
        );
    }

    #[test]
    fn generate_profile_level_id_for_answer_constrained_baseline_level_asymmetry() {
        let local_profile_level_id = "42e01f".parse::<ProfileLevelId>().ok();
        let local_level_asymmetry_allowed = true;

        let remote_profile_level_id = "42e015".parse::<ProfileLevelId>().ok();
        let remote_level_asymmetry_allowed = true;

        assert_eq!(
            generate_profile_level_id_for_answer(
                local_profile_level_id,
                local_level_asymmetry_allowed,
                remote_profile_level_id,
                remote_level_asymmetry_allowed
            ),
            Ok("42e01f".parse::<ProfileLevelId>().unwrap()),
        );
    }
}

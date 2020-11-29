# h264-profile-level-id

[![Build Status](https://img.shields.io/travis/com/nazar-pc/h264-profile-level-id/master?style=flat-square)](https://travis-ci.com/nazar-pc/h264-profile-level-id)
[![Crates.io](https://img.shields.io/crates/v/h264-profile-level-id?style=flat-square)](https://crates.io/crates/h264-profile-level-id)
[![Docs](https://img.shields.io/badge/docs-latest-blue.svg?style=flat-square)](https://docs.rs/h264-profile-level-id)
[![License](https://img.shields.io/github/license/nazar-pc/h264-profile-level-id?style=flat-square)](https://github.com/nazar-pc/h264-profile-level-id)

Idiomatic Rust port of <https://github.com/ibc/h264-profile-level-id> by Iñaki Baz Castillo.

Rust utility to process [H264](https://tools.ietf.org/html/rfc6184) `profile-level-id` values based on Google's [libwebrtc](https://chromium.googlesource.com/external/webrtc/+/refs/heads/master/media/base/h264_profile_level_id.h) C++ code.

## Basic usage example:
```rust
use h264_profile_level_id::{Profile, Level, ProfileLevelId};

fn main () {
    let profile_level_id: ProfileLevelId = "42e01f".parse().unwrap();
    
    assert_eq!(profile_level_id.profile(), Profile::ConstrainedBaseline);
    assert_eq!(profile_level_id.level(), Level::Level31);
    
    let s = profile_level_id.to_string();
    
    assert_eq!(s.as_str(), "42e01f");

    let local_profile_level_id = "42e01f".parse::<ProfileLevelId>().ok();
    let local_level_asymmetry_allowed = true;

    let remote_profile_level_id = "42e015".parse::<ProfileLevelId>().ok();
    let remote_level_asymmetry_allowed = true;

    assert_eq!(
        h264_profile_level_id::generate_profile_level_id_for_answer(
            local_profile_level_id,
            local_level_asymmetry_allowed,
            remote_profile_level_id,
            remote_level_asymmetry_allowed
        ),
        Ok("42e01f".parse::<ProfileLevelId>().unwrap()),
    );
}
```

## Contribution
Feel free to create issues and send pull requests, they are highly appreciated!

## License
ISC

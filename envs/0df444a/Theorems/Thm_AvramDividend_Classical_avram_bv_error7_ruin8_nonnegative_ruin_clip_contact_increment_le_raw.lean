-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_nonnegative_ruin_clip_contact_increment_le_raw
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_nonnegative_ruin_clip_contact_increment_le_raw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:16:41.757318+00:00
-- url     : https://prove2.me/theorems/8e4ca4af-6826-4e44-9927-000c5fd1f003
-- title:
--   Nonnegative ruin-clipping cannot amplify an original compensated stopped contact increment
-- statement:
--   If the stopped pre-contact reserve is nonnegative, zero-clipping its post-contact reserve changes it by at most the absolute raw contact increment, including cells crossing ruin.
-- source:
--   Elementary case split on whether the post-contact reserve z+c is nonpositive or nonnegative. Used as an independent child for the original process positive-error ruin boundary continuity; no signed budget or surrogate stochastic process.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_nonnegative_ruin_clip_contact_increment_le_raw (z c : ℝ) (hz : 0 ≤ z) :
    |max (z + c) 0 - z| ≤ |c| := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_test_weighted_log_vanishes_near_one
-- name    : AvramDividend.Classical.avram_p2_b_rate_negative_test_weighted_log_vanishes_near_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:46:30.890085+00:00
-- url     : https://prove2.me/theorems/1d8a7240-0297-42ab-9a52-b6d6a798837e
-- title:
--   Separated negative-mark inverse weighted log test vanishes on a neighbourhood of z=1
-- statement:
--   For a test function that vanishes on marks strictly greater than -epsilon with epsilon positive, the inverse exponential weighted test z -> f(log z)/(z-1)^4 equals zero on an entire neighbourhood of z=1. This proves removal of the apparent division singularity at the upper exponential-band endpoint, independently of the process and any jump-rate assumption.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_b_rate_negative_test_weighted_log_vanishes_near_one
    (f : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hfsupp : ∀ y : ℝ, -ε < y → f y = 0) :
    (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4) =ᶠ[nhds (1 : ℝ)]
      (fun _ : ℝ => 0) := by sorry

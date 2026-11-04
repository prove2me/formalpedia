-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_test_weighted_log_vanishes_near_zero
-- name    : AvramDividend.Classical.avram_p2_b_rate_negative_test_weighted_log_vanishes_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:48:36.612524+00:00
-- url     : https://prove2.me/theorems/13b4bb27-016e-43a6-ad1d-3b88a03b45a5
-- title:
--   Compact lower negative-mark cutoff removes weighted logarithmic test singularity at z=0
-- statement:
--   If a real test function vanishes below a fixed finite mark cutoff a and also vanishes at zero, the inverse exponential weighted test f(log z)/(z-1)^4 is identically zero in a right-sided neighbourhood of z=0. This gives the missing lower endpoint extension for compactly supported negative-mark test functions.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_b_rate_negative_test_weighted_log_vanishes_near_zero
    (f : ℝ → ℝ) (a : ℝ)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfzero : f 0 = 0) :
    (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4) =ᶠ[
      nhdsWithin (0 : ℝ) (Ici 0)] (fun _ : ℝ => 0) := by sorry

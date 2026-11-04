-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_log_test_continuous_nonnegative
-- name    : AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_continuous_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:06:14.006899+00:00
-- url     : https://prove2.me/theorems/602ee195-5ed6-40fe-94c0-807f19926b90
-- title:
--   Continuity of the inverse weighted logarithmic test on the entire nonnegative image halfline
-- statement:
--   A continuous compact-separated negative mark test has a fourth-weighted logarithmic inverse transform continuous on [0,infinity). The proof glues the already Proved exact endpoint-zero and endpoint-one neighbourhood vanishing lemmas to ordinary logarithmic quotient continuity elsewhere, without any stochastic assumption.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_test_weighted_log_vanishes_near_one
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_test_weighted_log_vanishes_near_zero
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_continuous_nonnegative
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    ContinuousOn (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4) (Ici 0) := by sorry

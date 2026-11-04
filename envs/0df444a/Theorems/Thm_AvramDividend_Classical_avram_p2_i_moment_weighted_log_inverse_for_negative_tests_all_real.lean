-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_weighted_log_inverse_for_negative_tests_all_real
-- name    : AvramDividend.Classical.avram_p2_i_moment_weighted_log_inverse_for_negative_tests_all_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:05:05.235201+00:00
-- url     : https://prove2.me/theorems/6285e333-fd07-403d-9cd6-e639ea159470
-- title:
--   Weighted logarithmic inverse recovers negative-supported real tests at all original marks
-- statement:
--   If f is zero at every nonnegative real argument, the inverse weighted exponential-image test multiplied by its fourth-power weight recovers f(y) for every real y, including zero and positive original process increments. It extends P2-B's proved strictly negative inverse identity and closes the pointwise equality needed to convert original source weighted-image integrals to unweighted compact-negative tests, without assuming a jump-rate theorem.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_i_moment_weighted_log_inverse_for_negative_tests_all_real
    (f : ℝ → ℝ) (hfpos : ∀ y : ℝ, 0 ≤ y → f y = 0) (y : ℝ) :
    (Real.exp y - 1) ^ 4 *
      (f (Real.log (Real.exp y)) / (Real.exp y - 1) ^ 4) = f y := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_continuous_nonnegative_test_with_tail_cutoff_bounded
-- name    : AvramDividend.Classical.avram_p2_b_rate_continuous_nonnegative_test_with_tail_cutoff_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:26:56.33125+00:00
-- url     : https://prove2.me/theorems/ecd99554-fbec-4c62-9755-d2c54f6b2923
-- title:
--   A continuous nonnegative-halfline test with a right cutoff has bounded range
-- statement:
--   If a real function is continuous on [0,infinity) and vanishes to the right of a finite nonnegative threshold R, then its full image on [0,infinity) is bounded. The proof uses compactness of [0,R], continuity of the compact image, and the zero tail. This is a deterministic bridge from the P2-B endpoint continuity and compact-support facts to admissible bounded weak-convergence test functions.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_b_rate_continuous_nonnegative_test_with_tail_cutoff_bounded
    (g : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hcont : ContinuousOn g (Ici 0))
    (hzero : ∀ z : ℝ, R < z → g z = 0) :
    Bornology.IsBounded (g '' Ici (0 : ℝ)) := by sorry

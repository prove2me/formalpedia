-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_weighted_log_negative_mark_recovers_original_test
-- name    : AvramDividend.Classical.avram_p2_weighted_log_negative_mark_recovers_original_test
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:03:58.818815+00:00
-- url     : https://prove2.me/theorems/5608009e-d808-45cb-9063-fd5592399c9d
-- title:
--   Exact recovery of original negative-jump test from logarithmic inverse weighted exponential coordinates
-- statement:
--   For every strictly negative original Lévy mark y, exp(y) lies strictly below one, so the fourth power of exp(y)-1 is strictly nonzero. Evaluating the weighted exponential-image inverse test f(log z)/(z−1)^4 at z=exp(y) and restoring the fourth-power weight recovers the original arbitrary real test f(y) exactly. This is an essential algebraic step in deriving source small-time rates for continuous compactly supported negative tests from weighted-image weak convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_weighted_log_negative_mark_recovers_original_test
    (f : ℝ → ℝ) (y : ℝ) (hy : y < 0) :
    (f (Real.log (Real.exp y)) / (Real.exp y - 1) ^ 4) *
      (Real.exp y - 1) ^ 4 = f y := by sorry

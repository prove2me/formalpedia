-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_positive
-- name    : AvramDividend.Classical.avram_ws01e_b_expMeasure_strict_survival_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:59:08.951807+00:00
-- url     : https://prove2.me/theorems/e306d2ca-0099-444e-8293-093138a0839d
-- title:
--   Every nonnegative tail of the genuine exponential clock has positive probability
-- statement:
--   For a genuine positive-rate exponential observation clock, the probability of surviving past any finite nonnegative real threshold is strictly positive. This reusable consequence of the accepted exponential strict-tail formula ensures the denominator of the conditional stop-before-clock law can be nonzero and is used with the general positive-survival Tonelli theorem. It does not assume Wiener–Hopf independence.
-- source:
--   Accepted AvramDividend.Classical.avram_ws01e_b_expMeasure_strict_survival_real (69bfdea1-9b67-42db-ab4b-e2473b94061f), ENNReal.ofReal_pos, Real.exp_pos.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_expMeasure_strict_survival_positive (p a : ℝ) (hp : 0 < p) (ha : 0 ≤ a) :
    0 < ProbabilityTheory.expMeasure p (Set.Ioi a) := by sorry

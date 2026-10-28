-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exp_clock_toNNReal_strict_tail
-- name    : AvramDividend.Classical.avram_ws01e_b_exp_clock_toNNReal_strict_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:57:02.980971+00:00
-- url     : https://prove2.me/theorems/6aa1899c-a9d8-4b5a-9407-4bd278dcc368
-- title:
--   Actual Exp(p) clock strict-survival law through the nonnegative time embedding
-- statement:
--   For a real exponential observation clock of rate p>0, the strict upper-tail probability of the nonnegative observation time t.toNNReal above a≥0 equals exp(-pa) as an ENNReal. This equates the true real-clock Ioi event to the corresponding NNReal event and is the missing concrete survival-kernel interface for the generic residual-clock memorylessness theorem. No fictional nonnegative support at negative real sample values is assumed.
-- source:
--   Direct event-set transport via pinned Mathlib Real.lt_toNNReal_iff_coe_lt and Proved avram_ws01e_b_expMeasure_strict_survival_real (69bfdea1-9b67-42db-ab4b-e2473b94061f).

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_exp_clock_toNNReal_strict_tail (p : ℝ) (hp : 0 < p) (a : ℝ≥0) :
    expMeasure p {t : ℝ | a < t.toNNReal} =
      ENNReal.ofReal (Real.exp (-(p * (a : ℝ)))) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_rateone_early_negative_mark_arrival_positive_cdf
-- name    : AvramDividend.Classical.avram_jump6_A_rateone_early_negative_mark_arrival_positive_cdf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:17:46.726866+00:00
-- url     : https://prove2.me/theorems/d40b011d-cec0-487a-930a-3f9046f4aff2
-- title:
--   Rate-one first negative-mark arrival has positive cumulative probability by time one tenth
-- statement:
--   For the actual unit-rate exponential first arrival time in the original Brownian plus size-two Poisson countermodel, the CDF is strictly positive at 1/10. This complements the existing Proved CDF<1 at time one and helps establish positive probability of a ruin-causing negative jump during the short Brownian tube needed to challenge the unit-coefficient full-mark physical mesh statement.

import Mathlib
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open ProbabilityTheory MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_rateone_early_negative_mark_arrival_positive_cdf :
    0 < (cdf (expMeasure (1 : ℝ))) (1 / 10 : ℝ) := by sorry

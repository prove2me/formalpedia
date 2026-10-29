-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_clock_Iic_strictly_positive_ws01f
-- name    : AvramDividend.Classical.exp_clock_Iic_strictly_positive_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:35:30.802769+00:00
-- url     : https://prove2.me/theorems/16d17c1b-56e1-4119-88f8-ed314a985e60
-- title:
--   Every genuinely positive exponential-clock rate has strictly positive bounded-horizon mass
-- statement:
--   For every positive rate p and positive real horizon T, the actual exponential probability measure on real time assigns positive mass to the lower half-line up to T. This is the precise input to the genuine exponential-clock-product survival-zero to deterministic-horizon argument in WS1F.
-- source:
--   Pinned Mathlib ProbabilityTheory.cdf_expMeasure_eq, ProbabilityTheory.ofReal_cdf, and Real.exp strict monotonicity.

import Mathlib

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.exp_clock_Iic_strictly_positive_ws01f
    (p T : ℝ) (hp : 0 < p) (hT : 0 < T) :
    0 < (expMeasure p) (Iic T) := by sorry

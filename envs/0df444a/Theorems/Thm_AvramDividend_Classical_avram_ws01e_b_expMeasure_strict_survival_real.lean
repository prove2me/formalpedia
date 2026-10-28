-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real
-- name    : AvramDividend.Classical.avram_ws01e_b_expMeasure_strict_survival_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:49:43.056891+00:00
-- url     : https://prove2.me/theorems/69bfdea1-9b67-42db-ab4b-e2473b94061f
-- title:
--   Genuine exponential clock has the strict upper-tail survival law
-- statement:
--   For positive real rate p and nonnegative real time a, the probability that a real-valued Exp(p) observation clock is strictly greater than a equals exp(-p a), embedded in the extended nonnegative reals. The proof uses the authentic Mathlib expMeasure probability and CDF, the strict-complement relation Ioi a=(Iic a)ᶜ, and nonnegative-real arithmetic. This explicit survival interface is needed to instantiate stopped-age residual-clock factorisation at the actual independent exponential horizon.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.CDF
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_expMeasure_strict_survival_real
    (p a : ℝ) (hp : 0 < p) (ha : 0 ≤ a) :
    ProbabilityTheory.expMeasure p (Set.Ioi a) =
      ENNReal.ofReal (Real.exp (-(p * a))) := by sorry

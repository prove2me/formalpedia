-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_exponential_halfline_laplace
-- name    : AvramDividend.Classical.positive_exponential_halfline_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T00:22:31.30032+00:00
-- url     : https://prove2.me/theorems/894d8b35-8478-4f99-8e7f-6bb93c7720f4
-- title:
--   Laplace mass of exponential kernel on the positive half-line
-- statement:
--   For every positive θ, the nonnegative integral of exp(-θx) over the positive real half-line is 1/θ. This converts the pinned real improper exponential integral into an extended nonnegative Laplace-transform identity, needed to build the positive exponential baseline kernel Eφ(dt)=exp(φt)dt, and hence the factored renewal series proving positive exponential normalisation of bounded-variation q-scale functions.
-- source:
--   Pinned Mathlib Analysis/SpecialFunctions/ImproperIntegrals.lean integrableOn_exp_mul_Ioi, integral_exp_mul_Ioi and MeasureTheory.ofReal_integral_eq_lintegral_ofReal

import Mathlib
open MeasureTheory Set Real
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The discounted exponential kernel on the positive half-line has
extended nonnegative Laplace mass equal to the reciprocal discount. -/
theorem positive_exponential_halfline_laplace (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-θ * x))) =
      ENNReal.ofReal (1 / θ) := by
  sorry

end AvramDividend.Classical

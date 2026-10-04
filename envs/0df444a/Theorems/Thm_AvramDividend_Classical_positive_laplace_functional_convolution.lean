-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_laplace_functional_convolution
-- name    : AvramDividend.Classical.positive_laplace_functional_convolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:54:41.320408+00:00
-- url     : https://prove2.me/theorems/5aa47d4f-3286-4290-a0f4-1f910e0dc1a3
-- title:
--   Positive Laplace integrals multiply under additive measure convolution
-- statement:
--   For any measures μ and ν on the real additive group with ν s-finite, the extended nonnegative Laplace functional Lθ(μ)=∫ exp(−θx) μ(dx) is multiplicative under additive convolution: Lθ(μ*ν)=Lθ(μ)Lθ(ν). This is the exact geometric-transform identity needed to sum convolution powers of the finite discounted renewal kernel ρ in the bounded-variation scale-function construction. The identity holds without bounded support and without assuming finite integrals, because all functions are nonnegative.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_conv, lintegral_const_mul, lintegral_mul_const, ENNReal.ofReal_mul and Real.exp_add

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The positive exponential Laplace functional is multiplicative
under convolution of real measures, using nonnegative integrals. -/
theorem positive_laplace_functional_convolution (μ ν : Measure ℝ) [SFinite ν] (θ : ℝ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-θ * z))
       ∂Measure.conv μ ν) =
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂μ) *
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-θ * y)) ∂ν) := by
  sorry

end AvramDividend.Classical

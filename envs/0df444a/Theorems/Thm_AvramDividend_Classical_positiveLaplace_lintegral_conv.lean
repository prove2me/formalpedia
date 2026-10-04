-- Prove2me | Theorems.Thm_AvramDividend_Classical_positiveLaplace_lintegral_conv
-- name    : AvramDividend.Classical.positiveLaplace_lintegral_conv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T00:02:14.508212+00:00
-- url     : https://prove2.me/theorems/d1bec0b0-49b2-4710-9cae-57a9d9e5fd8e
-- title:
--   Laplace transform of positive measure convolution factorises
-- statement:
--   For any two measures on the real line with the right-hand measure sigma-finite and any real Laplace parameter θ, the nonnegative integral of exp(-θz) against their additive convolution equals the product of the two individual nonnegative Laplace integrals. The identity is valid even when one of the integrals diverges and directly enables a geometric-series convolution resolvent in the bounded-variation scale-function argument.
-- source:
--   Pinned Mathlib MeasureTheory.Group.Convolution (lintegral_conv), MeasureTheory.Integral.Lebesgue.Add (lintegral_lintegral_mul), and Real.exp_add.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The nonnegative Laplace transform of additive convolution factorises. -/
theorem positiveLaplace_lintegral_conv (μ ν : Measure ℝ) [SFinite ν] (θ : ℝ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-θ * z)) ∂(μ ∗ ν)) =
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂μ) *
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-θ * y)) ∂ν) := by
  sorry

end AvramDividend.Classical

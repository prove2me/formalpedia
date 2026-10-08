-- Prove2me | Theorems.Thm_AvramDividend_Classical_weightedLaplace_integral_shift_real
-- name    : AvramDividend.Classical.weightedLaplace_integral_shift_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:07:40.112998+00:00
-- url     : https://prove2.me/theorems/2f693a4a-56b1-426d-a2c3-b51f47544f58
-- title:
--   Translation identity for the full-line exponentially weighted Laplace integral
-- statement:
--   For any real function f and any real theta and shift y, translation invariance of Lebesgue integration gives ∫_R exp(-theta*x) f(x+y) dx = exp(theta*y) ∫_R exp(-theta*x) f(x) dx (with the Lebesgue integral convention for nonintegrable functions). This is a general measure-theoretic step used when taking the Laplace transform of the negative-jump Levy generator acting on a scale function W, which vanishes on the negative half-line.
-- source:
--   Change of variables x↦x+y in the Laplace-transform calculation for the spectrally negative Lévy generator; an independent consequence of Mathlib Lebesgue-integral translation invariance.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem weightedLaplace_integral_shift_real
    (f : ℝ → ℝ) (θ y : ℝ) :
    (∫ x : ℝ, Real.exp (-(θ * x)) * f (x + y)) =
      Real.exp (θ * y) *
        (∫ x : ℝ, Real.exp (-(θ * x)) * f x) := by sorry

end AvramDividend.Classical

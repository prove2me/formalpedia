-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_derivative_strictly_positive
-- name    : AvramDividend.Classical.excursion_derivative_strictly_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:11:52.350346+00:00
-- url     : https://prove2.me/theorems/9388995d-0962-4758-b422-b5263be49f41
-- title:
--   The excursion-height representation makes the scale-function derivative strictly positive
-- statement:
--   If W>0 on positive arguments and its derivative satisfies W′(x)=W(x)(φ+μ([x,∞))) for some φ>0 and positive measure μ, then W′(x)>0 for every x>0. The excursion height tail is nonnegative, so the bracket is at least the positive root φ. This is the positivity consequence needed for barrier value denominators and scale-function shape, independent of the hard measure construction.
-- source:
--   Excursion-height derivative representation and ENNReal.toReal_nonneg; source-neutral positivity.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.excursion_derivative_strictly_positive
    (W : ℝ → ℝ) (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hW : ∀ x : ℝ, 0 < x → 0 < W x)
    (hderiv : ∀ x : ℝ, 0 < x → deriv W x = W x * (φ + μ.real (Ici x))) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by sorry

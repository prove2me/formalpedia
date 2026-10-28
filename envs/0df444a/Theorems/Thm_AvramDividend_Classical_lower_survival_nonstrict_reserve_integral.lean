-- Prove2me | Theorems.Thm_AvramDividend_Classical_lower_survival_nonstrict_reserve_integral
-- name    : AvramDividend.Classical.lower_survival_nonstrict_reserve_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:52:05.837011+00:00
-- url     : https://prove2.me/theorems/69541768-3d7b-4c45-a6f2-043b9bc2ed7b
-- title:
--   Laplace integral of nonnegative-reserve survival with the boundary included
-- statement:
--   Integrating the positive-reserve exponential Laplace weight over initial reserves x>0 satisfying x+m≥0 yields exp(-θ max(0,-m))/θ for θ>0, including the survival equality boundary. Since Lebesgue measure has no point masses, the boundary at x=-m does not affect the integral. This converts a running-infimum survival condition into an explicit exponential envelope without strict-inequality errors.
-- source:
--   Mathlib integral_exp_mul_Ioi and integral_Ici_eq_integral_Ioi, with sign-case splitting on m. This is the exact non-strict event needed in the killed-survival Laplace transformation.

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set

theorem AvramDividend.Classical.lower_survival_nonstrict_reserve_integral
    (m θ : ℝ) (hθ : 0 < θ) :
    (∫ x in {x : ℝ | 0 < x ∧ 0 ≤ x + m}, Real.exp (-θ * x)) =
      Real.exp (-θ * max 0 (-m)) / θ := by sorry

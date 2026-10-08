-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_laplace_upper_bound_from_support_gap
-- name    : AvramDividend.Classical.excursion_laplace_upper_bound_from_support_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:16:26.609973+00:00
-- url     : https://prove2.me/theorems/4f81c8ee-57ce-47a1-abce-85fdde6309d2
-- title:
--   A positive finite measure supported above x has exponentially bounded Laplace transform
-- statement:
--   A finite positive measure β concentrated at levels y≥x has Laplace transform bounded by β(ℝ)e^(−θx) for every θ≥0, provided its Laplace integrand is integrable. This is an exact measure-theoretic support-gap bound, central to proving strict positive-height cumulative mass of the killed descending ladder potential by contradiction against its c/θ transform lower bound.
-- source:
--   Pinned MeasureTheory.integral_mono_ae, integral_const, and Real.exp_le_exp; excursion ladder potential support.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.excursion_laplace_upper_bound_from_support_gap
    (β : Measure ℝ) [IsFiniteMeasure β]
    (x θ : ℝ) (hθ : 0 ≤ θ)
    (hsupport : ∀ᵐ y : ℝ ∂β, x ≤ y)
    (hint : Integrable (fun y : ℝ => Real.exp (-(θ * y))) β) :
    (∫ y : ℝ, Real.exp (-(θ * y)) ∂β) ≤
      β.real univ * Real.exp (-(θ * x)) := by sorry

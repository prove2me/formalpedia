-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_killed_potential_full_support_from_eventual_laplace_lower_bound
-- name    : AvramDividend.Classical.excursion_killed_potential_full_support_from_eventual_laplace_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:27:33.421693+00:00
-- url     : https://prove2.me/theorems/f0be2575-cad1-489c-b1f0-9381f0cf56b5
-- title:
--   Finite killed ladder potentials with reciprocal Laplace lower bounds for s at least one charge all positive initial intervals
-- statement:
--   If a finite positive measure β has an integrable Laplace transform and a lower bound c/θ only for θ≥1, then it must charge every initial interval (−∞,x] with x>0. This sharpens the earlier too-strong all-positive-parameter theorem and exactly matches the killed Bernstein exponent estimate F(θ)≤Cθ for θ≥1. The proof derives a support gap from zero initial mass, applies the exponential integral envelope, then chooses θ≥1 where exponential decay beats inverse-linear decay.
-- source:
--   Published excursion_laplace_exponential_beats_inverse_above_one, excursion_zero_cumulative_mass_implies_ae_support_gap, excursion_laplace_upper_bound_from_support_gap.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.excursion_killed_potential_full_support_from_eventual_laplace_lower_bound
    (β : Measure ℝ) [IsFiniteMeasure β] (c : ℝ) (hc : 0 < c)
    (hint : ∀ θ : ℝ, 1 ≤ θ →
      Integrable (fun y : ℝ => Real.exp (-(θ * y))) β)
    (hlower : ∀ θ : ℝ, 1 ≤ θ →
      c / θ ≤ ∫ y : ℝ, Real.exp (-(θ * y)) ∂β) :
    ∀ x : ℝ, 0 < x → 0 < β (Iic x) := by sorry

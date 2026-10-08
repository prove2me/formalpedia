-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_killed_ladder_potential_full_support_from_laplace_lower_bound
-- name    : AvramDividend.Classical.excursion_killed_ladder_potential_full_support_from_laplace_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:18:03.586672+00:00
-- url     : https://prove2.me/theorems/314691a6-4c64-4508-9e2c-0bf6bd18e9f1
-- title:
--   Finite killed-ladder potential with reciprocal-linear Laplace bound charges every positive-height initial interval
-- statement:
--   If β is any finite positive measure whose real Laplace transform is integrable and bounded below by c/θ for all θ>0 with c>0, then β gives positive mass to (−∞,x] for every x>0. Indeed, if β had no mass below x, its transform would be at most β(ℝ)e^(−θx), conflicting with c/θ as θ→∞. This is the full-support lemma needed for the Gaussian no-atom killed-descending-ladder potential. It is a genuine measure-theoretic theorem independent of proving existence of that stochastic potential.
-- source:
--   Pinned Mathlib MeasureTheory.ae_iff, integral_mono_ae, integral_const, Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero, and three newly published excursion support helper proofs.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.excursion_killed_ladder_potential_full_support_from_laplace_lower_bound
    (β : Measure ℝ) [IsFiniteMeasure β] (c : ℝ) (hc : 0 < c)
    (hint : ∀ θ : ℝ, 0 < θ →
      Integrable (fun y : ℝ => Real.exp (-(θ * y))) β)
    (hlower : ∀ θ : ℝ, 0 < θ →
      c / θ ≤ ∫ y : ℝ, Real.exp (-(θ * y)) ∂β) :
    ∀ x : ℝ, 0 < x → 0 < β (Iic x) := by sorry

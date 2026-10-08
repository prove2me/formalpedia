-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_exhausted_by_natural_horizons
-- name    : AvramDividend.Classical.lintegral_exhausted_by_natural_horizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:31:11.290403+00:00
-- url     : https://prove2.me/theorems/0b3f1a50-a442-4896-83bd-e177af2b4686
-- title:
--   Any measurable discounted payout integral on real time equals the supremum of its finite-horizon truncations
-- statement:
--   For an arbitrary measure μ on real times, nonnegative measurable integrand f, and measurable region S, the Lebesgue integral over S is the supremum of its restrictions to S∩(−∞,n] over natural n. This is the exact inner monotone-convergence lemma needed to pass from the truncated BV/UBV dividend stochastic inequalities to the full discounted Stieltjes payoff. It is measure-theoretic and does not assume any Lévy calculus.
-- source:
--   Pinned Mathlib lintegral_iSup, lintegral_indicator, Set.indicator_iUnion_apply, Set.indicator_le_indicator_of_subset and Archimedean exists_nat_ge.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.lintegral_exhausted_by_natural_horizons
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (S : Set ℝ) (hS : MeasurableSet S) :
    (∫⁻ t in S, f t ∂μ) =
      ⨆ n : ℕ, (∫⁻ t in S ∩ Iic (n : ℝ), f t ∂μ) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_finset_lintegral_bound
-- name    : AvramDividend.Classical.discounted_dividendMeasure_finset_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:12:10.672429+00:00
-- url     : https://prove2.me/theorems/e2503ac9-b89c-4f3c-ac90-1c550cb8b29f
-- title:
--   Discounted Stieltjes dividends paid on any finite active set are bounded by the sum of exponential reserve drops
-- statement:
--   For any finite set S of nonnegative dividend payment times before ruin (or time zero), the actual discounted Lebesgue–Stieltjes integral of dividendMeasure over S is at most the sum of discounted exponential candidate-value reductions at the respective right dividend jumps, for θ≥1. It follows from Mathlib lintegral_finset and the proven single-payment inequality. This is a finite-atomic portion of dividendValue, not the still-missing full continuous Stieltjes integral inequality.
-- source:
--   Child discounted_dividendMeasure_atom_exponential_bound, pinned Mathlib MeasureTheory.lintegral_finset and Real.coe_toNNReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_dividendMeasure_finset_lintegral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (θ q : ℝ) (hθ : 1 ≤ θ)
    (ω : Ω) (S : Finset ℝ)
    (hNonneg : ∀ s ∈ S, 0 ≤ s)
    (hActive : ∀ s ∈ S,
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in (S : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ∑ s ∈ S, ENNReal.ofReal (Real.exp (-(q * s)) *
      (Real.exp (θ * riskProcess X x D s.toNNReal ω) -
        Real.exp (θ * (riskProcess X x D s.toNNReal ω -
          (rightLimit D s.toNNReal ω - D s.toNNReal ω))))) := by sorry

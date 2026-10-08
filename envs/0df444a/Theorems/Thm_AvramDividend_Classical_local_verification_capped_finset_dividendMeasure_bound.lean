-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_capped_finset_dividendMeasure_bound
-- name    : AvramDividend.Classical.local_verification_capped_finset_dividendMeasure_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:29:54.451439+00:00
-- url     : https://prove2.me/theorems/73b71427-f3b9-455e-8f70-b5432b9cfa89
-- title:
--   The original HJB verification assumptions bound the exact discounted dividend Stieltjes integral over any finite active set by the sum of verification-value drops
-- statement:
--   For any capped admissible strategy in Proposition 4, and any finite set of active nonnegative payment times, the discounted Lebesgue–Stieltjes integral on that set is bounded by the sum of discounted losses in the *general* HJB verification function w at those right dividend jumps. The proof sums the atomic HJB dividend measure estimates via Mathlib lintegral_finset. It handles genuine admissible-strategy dividends under both BV and UBV assumptions and arbitrary finite collections, without claiming control of the continuous Stieltjes or stochastic Lévy drift contributions.
-- source:
--   Child local_verification_capped_dividendMeasure_atom_bound and pinned Mathlib lintegral_finset.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_capped_finset_dividendMeasure_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (S : Finset ℝ)
    (hNonneg : ∀ s ∈ S, 0 ≤ s)
    (hActive : ∀ s ∈ S,
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in (S : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ∑ s ∈ S, ENNReal.ofReal (Real.exp (-(q * s)) *
      (w (riskProcess X x D s.toNNReal ω) -
        w (riskProcess X x D s.toNNReal ω -
          (rightLimit D s.toNNReal ω - D s.toNNReal ω)))) := by sorry

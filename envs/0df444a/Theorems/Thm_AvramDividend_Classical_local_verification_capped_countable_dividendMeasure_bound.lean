-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_capped_countable_dividendMeasure_bound
-- name    : AvramDividend.Classical.local_verification_capped_countable_dividendMeasure_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:07:05.15856+00:00
-- url     : https://prove2.me/theorems/ddcbaba7-493c-430c-8312-7c54e75e21be
-- title:
--   Under the general HJB local-verification assumptions, discounted Stieltjes dividends on every countable active set are bounded by a sum of candidate-value drops
-- statement:
--   For any capped admissible strategy, and any countable set S of active nonnegative payment times, the true discounted Stieltjes integral over S is no larger than the nonnegative infinite sum over S of discounted decreases of the general HJB test function w at the corresponding right dividend jumps. This is an extension of the accepted finite-set argument to arbitrary countably many atoms using Mathlib's exact countable lintegral formula and ENNReal.tsum_le_tsum. It handles the entire atomic payout component once its countable support is identified, without asserting anything about the non-atomic component or Dynkin/Itô terms.
-- source:
--   Child local_verification_capped_dividendMeasure_atom_bound; pinned Mathlib MeasureTheory.lintegral_countable and ENNReal.tsum_le_tsum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_capped_countable_dividendMeasure_bound
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
    (ω : Ω) (S : Set ℝ) (hCountable : S.Countable)
    (hNonneg : ∀ s ∈ S, 0 ≤ s)
    (hActive : ∀ s ∈ S,
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in S,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ∑' s : S, ENNReal.ofReal (Real.exp (-(q * (s : ℝ))) *
      (w (riskProcess X x D (s : ℝ).toNNReal ω) -
        w (riskProcess X x D (s : ℝ).toNNReal ω -
          (rightLimit D (s : ℝ).toNNReal ω - D (s : ℝ).toNNReal ω)))) := by sorry

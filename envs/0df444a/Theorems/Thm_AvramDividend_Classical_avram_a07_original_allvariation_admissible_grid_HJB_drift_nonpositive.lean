-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_original_allvariation_admissible_grid_HJB_drift_nonpositive
-- name    : AvramDividend.Classical.avram_a07_original_allvariation_admissible_grid_HJB_drift_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:36:38.748414+00:00
-- url     : https://prove2.me/theorems/025d789c-f935-4319-a26c-817cd3e1c5a5
-- title:
--   Arbitrary-variation original admissible-grid HJB drift sign
-- statement:
--   The exact finite-grid original reserve generator and dividend gradient drift is nonpositive for any spectral-negative Levy driver. Original admissibility yields pathwise dividend increments; bounded-variation was unused by the accepted proof.
-- source:
--   Premise generalisation of accepted source 09743d18-79c3-46a8-99ef-fc4c520e57b1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a07_original_allvariation_admissible_grid_HJB_drift_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) 
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (cells : Finset ℕ)
    (hregion : ∀ i ∈ cells,
      0 < riskProcess X x D (u i) ω ∧
        ENNReal.ofReal (riskProcess X x D (u i) ω) < C) :
    (∑ i ∈ cells,
      Real.exp (-(q * (u i : ℝ))) *
        (((u (i + 1) : ℝ) - (u i : ℝ)) *
          (X.generator w (riskProcess X x D (u i) ω) -
            q * w (riskProcess X x D (u i) ω)) +
        (D (u (i + 1)) ω - D (u i) ω) *
          (1 - deriv w (riskProcess X x D (u i) ω)))) ≤ 0 := by sorry

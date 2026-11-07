-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f14_original_ennreal_finitecap_predictable_hjb_ae
-- name    : AvramDividend.Classical.avram_p4_f14_original_ennreal_finitecap_predictable_hjb_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:45:16.453873+00:00
-- url     : https://prove2.me/theorems/d131d07c-f6e6-4c24-985e-56bf25f6d897
-- title:
--   Original finite ENNReal capped UBV predictable generator HJB support
-- statement:
--   The authentic original finite ENNReal cap C becomes C.toReal without changing the Levy process, stopping clock or strategy. The public finite-realcap occupation theorem gives almost-everywhere strict interior pre-jump reserve, C² regularity, generator nonpositivity and dividend slope bound for any ruin-dominated original clock, directly matching the finite-cap F14 source hypotheses.
-- source:
--   Source-exact wrapper for public Proved a8b46313-adfa-4b01-96a3-3ec17cfd7554; pinned Mathlib ENNReal.ofReal_toReal and ENNReal.toReal_pos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_admissible_finitecap_predictable_hjb_ae
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f14_original_ennreal_finitecap_predictable_hjb_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0∞) (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < σ ω) →
      let y : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      (0 < y ∧ ENNReal.ofReal y < C) ∧
        ContDiffWithinAt ℝ 2 w
          {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} y ∧
        X.GeneratorIntegrable w y ∧
        X.generator w y - q * w y ≤ 0 ∧ 1 ≤ deriv w y := by sorry

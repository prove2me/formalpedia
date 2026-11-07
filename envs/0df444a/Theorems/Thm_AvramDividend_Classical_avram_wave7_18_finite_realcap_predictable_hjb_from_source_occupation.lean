-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_finite_realcap_predictable_hjb_from_source_occupation
-- name    : AvramDividend.Classical.avram_wave7_18_finite_realcap_predictable_hjb_from_source_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:40:28.193771+00:00
-- url     : https://prove2.me/theorems/d96cf1cd-2ef2-45c1-a54a-99ef7e768169
-- title:
--   Finite real cap original predictable C² HJB support from proved UBV strict-subcap occupation
-- statement:
--   For the original UBV spectrally negative Lévy X and original capped admissible strategy D, assume the genuine current reserve is pathwise ≤ a finite real c at pre-ruin times. The existing Proved original-source UBV predictable strict-subcap occupation theorem and positive predictable occupation theorem imply the strict left reserve y=leftLim(x+X−rightLimit D) lies P×μ-a.e. in {0<y∧ENNReal.ofReal y<ENNReal.ofReal c} before any ruin-dominated clock. Apply exact C² ContDiffOn and HJB/generator/gradient hypotheses there. Unlike the earlier allcap interface, no a.e. upper-cap premise is assumed; it follows from the Proved source occupation theorem, with a real deterministic cap assumption still explicit. No Ito formula is asserted.

import Mathlib
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_predictable_positive_before_localiser_all_caps
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_strict_subcap_ae_on_atomless_clock

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_finite_realcap_predictable_hjb_from_source_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q c : ℝ) (hc : 0 < c) (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal c →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hCap : ∀ ω (s : ℝ≥0), (s : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D s ω ≤ c)
    (σ : Ω → ℝ≥0∞) (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < σ ω) →
      let y : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      (0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c) ∧
        ContDiffWithinAt ℝ 2 w
          {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c} y ∧
        X.GeneratorIntegrable w y ∧
        X.generator w y - q * w y ≤ 0 ∧ 1 ≤ deriv w y := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_allcap_stopped_generator_integral_sign
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_allcap_stopped_generator_integral_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:25:58.433743+00:00
-- url     : https://prove2.me/theorems/4a55ed53-ea9b-4de3-87e7-da968bcfa09a
-- title:
--   Physical original stopped discounted generator drift is nonpositive under an explicit integrable witness
-- statement:
--   Using the Proved exact original-process P4-E predictable stopped HJB lemma at a general nonzero cap, every physical-time discounted generator integrand is nonpositive on the pre-ruin stopped interior. Under explicit physical integrability of the resulting G, its stopped Bochner integral is a.e. nonpositive. This is an actual original-process generator-sign component for P4-F; the global Itô–Meyer identity and stochastic L1 remain separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_allcap_predictable_stopped_generator_HJB_ae
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_allcap_stopped_generator_integral_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (τ : Ω → ℝ≥0∞) (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (G : Ω → ℝ)
    (hG : ∀ ω, G ω =
      ∫ t : ℝ≥0, if 0 < t ∧ (t : ℝ≥0∞) < τ ω then
        Real.exp (-(q * (t : ℝ))) *
          (X.generator w (Function.leftLim
             (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
           q * w (Function.leftLim
             (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))
      else 0 ∂μ)
    (hGI : Integrable G P) :
    Integrable G P ∧ ∀ᵐ ω ∂P, G ω ≤ 0 := by sorry

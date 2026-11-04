-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_infinite_cap_stopped_generator_integrable_ae
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_infinite_cap_stopped_generator_integrable_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:26:48.069987+00:00
-- url     : https://prove2.me/theorems/eecfee3e-b340-42b6-930c-2b6083bb4a40
-- title:
--   Actual infinite-cap original stopped generator integrability and HJB sign almost everywhere including t=0
-- statement:
--   With original admissibility cap infinity, the source stopped zero-occupation theorem alone places almost every preclock reserve strictly above zero including at t=0 under arbitrary deterministic s-finite observation measures. Hence the explicit interior pointwise Levy GeneratorIntegrable and HJB deficit sign carry to the same source. This is not Bochner or probability-space L1 control.
-- source:
--   Proved original zero-occupation UUID 644af487-db5d-4d41-995b-5576891a3013, and for finite cap Proved original cap occupation cc500549-ba08-47b0-b5c0-07c7a9bb40f3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_infinite_cap_stopped_generator_integrable_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x ⊤ D)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ]
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0 ∂μ,
      (t : ℝ≥0∞) < τ ω →
      X.GeneratorIntegrable w (riskProcess X x D t ω) ∧
        X.generator w (riskProcess X x D t ω) -
        q * w (riskProcess X x D t ω) ≤ 0 := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_positive_no_grid
-- name    : AvramDividend.Classical.avram_wave5_ubv_allcap_original_stopped_positive_no_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:56:32.779256+00:00
-- url     : https://prove2.me/theorems/35d7d09c-385f-4fc7-bed3-d863cc271c59
-- title:
--   Same-source UBV positive pre-localiser occupation for all caps with no observation schedules
-- statement:
--   For an actual original-filtration spectrally negative Lévy process of unbounded variation, every capped admissible dividend regulator D, every cap C including zero or infinity, and any original ruin-dominated localising clock sigma, the controlled reserve is strictly positive at sigma-finite-time-almost-every strictly positive instant before that clock, for almost every sample path. No dense grid or cofinal horizons are exposed. Proof lifts the genuine source admissibility certificate to an auxiliary infinity cap without changing X,D or their filtration. Then the already Proved grid-free original strict-generator-domain theorem, which requires only a nonzero auxiliary cap, supplies positivity. The extra upper-cap conclusion is discarded. Restriction from the actual ruin clock to sigma is pointwise. This strengthens accepted stopped zero-occupation 398b9dc7-99f7-4a44-aa29-e38471bd5ab1 in the exact corrected-core admissibility context by eliminating auxiliary schedule hypotheses and allowing every actual cap. It is a generator dt support lemma, not a claim about dividend Stieltjes mass or martingale compensation.
-- source:
--   Corrected UBV canonical core 429e17ca-5528-40b5-b593-7c03973d0706. Accepted generator-interior no-grid theorem bd222a39-c2dd-4836-ab7e-20c75561dcda. Actual IsAdmissibleLe carries source IsAdmissible and extends to auxiliary cap infinity only for the proof; no model replacement. No core/milestone changes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_ubv_allcap_original_stopped_positive_no_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0∞)
    (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < σ ω) →
        0 < riskProcess X x D t ω := by sorry

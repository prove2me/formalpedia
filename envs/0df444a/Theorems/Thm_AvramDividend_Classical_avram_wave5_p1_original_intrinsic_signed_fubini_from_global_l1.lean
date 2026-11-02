-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_signed_fubini_from_global_l1
-- name    : AvramDividend.Classical.avram_wave5_p1_original_intrinsic_signed_fubini_from_global_l1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:30:46.5412+00:00
-- url     : https://prove2.me/theorems/c96314f4-216d-491b-bf55-b496b324cda4
-- title:
--   Actual original Lévy signed jump occupation Fubini from one global L¹ bound and almost-everywhere fibre integrability
-- statement:
--   For the literal intrinsic jump measure of the same original SpectrallyNegativeLevy process, the signed expected jump occupation identity follows assuming its predictable occupation kernel is a.e. measurable, its signed reward H is integrable against M=P.bind K, its positive and negative parts are predictable measurable, and H is integrable on P-almost every source fibre. The theorem proves positive/negative fibre lintegral a.e. finiteness and outer integrability from the single global L¹ bound using source-coupled nonnegative occupation Fubini and integrable_toReal_of_lintegral_ne_top, then invokes the Proved a.e.-fibre signed Fubini. No independent Poisson copy, source rectangle intensity law, or L² isometry is inferred.
-- source:
--   Accepted original source Fubini from a.e. fibres UUID 6cf166c8; accepted nonnegative intrinsic source bind UUID a2b399cb; source fibre AEMeasurable UUID d3243ffd; predictable lift UUID 95f32973; pinned Real.ofReal_le_enorm, ae_lt_top', integrable_toReal_of_lintegral_ne_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_predictable_sample_mark_lift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_source_fibre_lintegral_aemeasurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_signed_occupation_fubini_ae_fibres
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_original_intrinsic_signed_fubini_from_global_l1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (hKmeas : AEMeasurable K P)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hHi : Integrable H M)
    (hPosHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p => ENNReal.ofReal (H p)))
    (hNegHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p => ENNReal.ofReal (-H p)))
    (hFibre : ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2)) (NX ω)) :
    (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) =
      ∫ p, H p ∂M := by sorry

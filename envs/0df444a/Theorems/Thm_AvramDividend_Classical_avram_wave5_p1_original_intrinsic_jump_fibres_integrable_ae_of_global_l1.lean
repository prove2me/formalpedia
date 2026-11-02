-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_fibres_integrable_ae_of_global_l1
-- name    : AvramDividend.Classical.avram_wave5_p1_original_intrinsic_jump_fibres_integrable_ae_of_global_l1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:33:15.299452+00:00
-- url     : https://prove2.me/theorems/0b07342b-ad3d-4baa-9e9b-47f0f0f47acd
-- title:
--   Actual Lévy intrinsic jump reward is integrable on almost every original source fibre from its expected occupation L¹ bound
-- statement:
--   For the literal original SpectrallyNegativeLevy intrinsic jump measure NX, suppose K is its a.e.-measurable pushforward into the original predictable marked sigma-algebra and M=P.bind K. If the original predictable real reward H is measurable and integrable against M, then H((t,ω),z) is integrable against the actual NXω for P-almost every sample ω. The proof uses nonnegative source norm occupation Fubini, finite global L¹ norm, ae_lt_top' for the fibre norm integral, and the samplewise predictable lift to obtain strong measurability on each good fibre. This discharges hFibre for the Proved signed source Fubini under natural integrability assumptions.
-- source:
--   Accepted nonnegative intrinsic source occupation bind a2b399cb, source predictable lift 95f32973, fibre lintegral AEMeasurable d3243ffd, pinned Measurable.enorm and ae_lt_top'.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_predictable_sample_mark_lift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_source_fibre_lintegral_aemeasurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_original_intrinsic_jump_fibres_integrable_ae_of_global_l1
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
    (hHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H)
    (hHi : Integrable H M) :
    ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2)) (NX ω) := by sorry

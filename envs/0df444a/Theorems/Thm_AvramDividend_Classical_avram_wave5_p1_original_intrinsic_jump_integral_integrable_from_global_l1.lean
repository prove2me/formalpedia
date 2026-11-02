-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_integral_integrable_from_global_l1
-- name    : AvramDividend.Classical.avram_wave5_p1_original_intrinsic_jump_integral_integrable_from_global_l1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:48:32.607652+00:00
-- url     : https://prove2.me/theorems/1d9f9461-2a4f-4fe7-ab42-550472ec4cb9
-- title:
--   Original stopped-compatible Lévy intrinsic signed jump integral is integrable on the actual probability space from global predictable occupation L¹ and a.e. source fibre integrability
-- statement:
--   For the original SpectrallyNegativeLevy jump measure NX on the unchanged original probability space, let K be its a.e.-measurable lift to the marked predictable sigma algebra and M=P.bind K. A predictable measurable real reward H integrable against M with almost-everywhere integrable source fibres has an integrable random signed jump integral ω ↦ ∫H((t,ω),z) NXω(dt,dz). This automatically supplies the actual-source outer L¹ assumption of the already Proved stopped rectangle compensation theorem. The norm and positive/negative expected source occupations, not an independent Poisson copy, control the conclusion.
-- source:
--   Proved a2b399cb original nonnegative intrinsic NX occupation Fubini, d3243ffd source fibre AEMeasurable, 95f32973 samplewise lift; pinned Real.ofReal_le_enorm and integrable_toReal_of_lintegral_ne_top; signed part identity previously compiled in 6cf166c8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_predictable_sample_mark_lift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_source_fibre_lintegral_aemeasurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_original_intrinsic_jump_integral_integrable_from_global_l1
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
    (hHm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H)
    (hFibre : ∀ᵐ ω ∂P, Integrable
      (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2)) (NX ω)) :
    Integrable (fun ω =>
      ∫ p, H ((p.1, ω), p.2) ∂(NX ω)) P := by sorry

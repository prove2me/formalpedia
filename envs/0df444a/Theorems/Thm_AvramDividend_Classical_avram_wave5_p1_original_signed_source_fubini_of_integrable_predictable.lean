-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_signed_source_fubini_of_integrable_predictable
-- name    : AvramDividend.Classical.avram_wave5_p1_original_signed_source_fubini_of_integrable_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:58:33.167196+00:00
-- url     : https://prove2.me/theorems/0a4556ca-2732-465f-8996-7b58c247aaf5
-- title:
--   Original intrinsic Lévy signed jump compensation expectation follows from predictable measurability and one global L¹ source-occupation bound
-- statement:
--   Let NX be the intrinsic jump measure of the original SpectrallyNegativeLevy X on the same probability space P, K its assumed a.e.-measurable lift into the original predictable marked sigma-algebra, and M=P.bind K. Every measurable predictable real reward H satisfying Integrable H M has exactly E_P[∫H((t,ω),z) NXω(dt,dz)] = ∫H dM. The proof derives positive/negative predictable measurability from H, almost-everywhere actual-source fibre integrability from global L¹, then invokes the strengthened original source signed Fubini theorem, which itself derives the remaining outer integrability and a.e. finiteness. Source intensity rectangles, original actual compensated L² isometry, and finite-horizon mass are still separate.
-- source:
--   Prepared two source-specific children: global-L¹ signed Fubini (publication 1b9027d1) and original NX a.e. fibre L¹ (publication bc3edcc8); pinned ENNReal.measurable_ofReal.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_signed_fubini_from_global_l1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_fibres_integrable_ae_of_global_l1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_original_signed_source_fubini_of_integrable_predictable
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
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H) :
    (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) =
      ∫ p, H p ∂M := by sorry

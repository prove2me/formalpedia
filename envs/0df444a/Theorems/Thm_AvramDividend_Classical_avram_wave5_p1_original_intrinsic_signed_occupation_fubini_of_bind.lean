-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_signed_occupation_fubini_of_bind
-- name    : AvramDividend.Classical.avram_wave5_p1_original_intrinsic_signed_occupation_fubini_of_bind
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:44:25.643617+00:00
-- url     : https://prove2.me/theorems/53b748dd-8d0f-4f3c-9378-683db1665da7
-- title:
--   Original Lévy intrinsic signed jump occupation satisfies source Fubini under explicit finite positive/negative fibre integrability
-- statement:
--   With the unchanged original SpectrallyNegativeLevy sample paths and their literal intrinsic jump measure NX, define the expected source marked occupation measure M as the bind of original P with its lifted jump-measure kernel. Under explicit AEMeasurable measure-kernel, signed integrability, fibre integrability, measurability and finiteness of the positive/negative inner nonnegative integrals, the iterated actual-source signed jump reward has exactly the integral against M. This discharges the signed source Fubini hypothesis in the Proved stopped predictable source compensation theorem f544dab9, without assuming that equality. It still requires the independent original source intensity rectangle theorem and source kernel measurability.
-- source:
--   Composes Proved nonnegative actual-source occupation Fubini a2b399cb-efbd-4522-b560-a6e7e55207e7, Proved predictable fixed-sample lift 95f32973-4d5b-4174-b17c-29d5c210715c, pinned Mathlib integral_toReal and integral_eq_lintegral_pos_part_sub_lintegral_neg_part.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_occupation_lintegral_bind
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_predictable_sample_mark_lift_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_original_intrinsic_signed_occupation_fubini_of_bind
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
    (hFibre : ∀ ω, Integrable
      (fun p : ℝ≥0 × ℝ => H ((p.1, ω), p.2)) (NX ω))
    (hPosAem : AEMeasurable (fun ω =>
      ∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)) P)
    (hNegAem : AEMeasurable (fun ω =>
      ∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)) P)
    (hPosFin : ∀ᵐ ω ∂P,
      (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)) < ∞)
    (hNegFin : ∀ᵐ ω ∂P,
      (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)) < ∞)
    (hPosI : Integrable (fun ω =>
      (∫⁻ p, ENNReal.ofReal (H ((p.1, ω), p.2)) ∂(NX ω)).toReal) P)
    (hNegI : Integrable (fun ω =>
      (∫⁻ p, ENNReal.ofReal (-H ((p.1, ω), p.2)) ∂(NX ω)).toReal) P) :
    (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) =
      ∫ p, H p ∂M := by sorry

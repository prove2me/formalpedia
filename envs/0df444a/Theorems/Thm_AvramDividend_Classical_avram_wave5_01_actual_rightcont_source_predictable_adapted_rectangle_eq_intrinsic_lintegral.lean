-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_source_predictable_adapted_rectangle_eq_intrinsic_lintegral
-- name    : AvramDividend.Classical.avram_wave5_01_actual_rightcont_source_predictable_adapted_rectangle_eq_intrinsic_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:31:01.661373+00:00
-- url     : https://prove2.me/theorems/9b57a0a5-8c50-4fb1-9a05-47ab01f5cd6d
-- title:
--   Actual right-continuous original predictable adapted marked rectangles equal the same-path jump-count integral
-- statement:
--   For the genuine SpectrallyNegativeLevy P 𝓕 and its actual right-continuous filtration, the pointwise lifted intrinsic source kernel Kω is the original left-limit marked jump measure on the same Ω. If M=P.bind K, then for any A∈𝓕.rightCont_s and Borel marks B, the predictable occupation M(((s,t]×A)×B) equals ∫_A N_Xω((s,t]×B)dP, not merely in distribution. Measurability of the original rightCont kernel and predictable lift is discharged by proved source theorems. This is the exact source same-path adaptedness interface to pair with any independently proved negative-mark Lévy intensity; no such intensity or abstract Poisson space is assumed here.
-- source:
--   Specialise proved original rightCont kernel measurability fd94, original joint lift with filtration 𝓕.rightCont and same map_apply/bind_apply proof as canonical raw source f712. Novel premise A∈𝓕.rightCont_s cannot be recovered by the raw-filtration theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_rightcont_predictable_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_01_actual_rightcont_source_predictable_adapted_rectangle_eq_intrinsic_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (s t : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    M (((Ioc s t) ×ˢ A) ×ˢ B) =
      (∫⁻ ω in A,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          ((Ioc s t) ×ˢ B) ∂P) := by sorry

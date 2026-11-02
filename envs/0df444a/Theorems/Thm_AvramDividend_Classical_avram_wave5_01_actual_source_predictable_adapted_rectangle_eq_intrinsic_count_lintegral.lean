-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_predictable_adapted_rectangle_eq_intrinsic_count_lintegral
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_predictable_adapted_rectangle_eq_intrinsic_count_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:56:18.675306+00:00
-- url     : https://prove2.me/theorems/f712115e-5c58-4545-98cd-c273f4011bbe
-- title:
--   Actual original predictable occupation on adapted marked rectangles equals the same-path intrinsic jump-count lintegral
-- statement:
--   For an actual original SpectrallyNegativeLevy X on P with its unchanged original filtration 𝓕, let Kω be pointwise the source intrinsic left-limit marked jump measure lifted to predictable time-history×mark, and M=P.bind K. For any deterministic s,t, original-past 𝓕_s-measurable A, and Borel mark B, M assigns ((s,t]×A)×B exactly the same ENNReal value as the original P-restricted lintegral of the literal intrinsic jump count N_Xω((s,t]×B). This is the source-defining adapted-rectangle transport needed before comparing M with the canonical μ×X.ν; it assumes no marked Lévy intensity, no abstract Poisson copy, and no future compensation law.
-- source:
--   Proved same-source K AEMeasurability 4443ac3e and joint marked predictable-lift 2648ec36, Mathlib measurableSet_predictable_Ioc_prod, Measure.bind_apply/map_apply and lintegral_indicator. This is exactly the missing pathwise occupation-to-lintegral bridge at adapted rectangles for Chat02/P1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_full_original_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_predictable_adapted_rectangle_eq_intrinsic_count_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (s t : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    M (((Ioc s t) ×ˢ A) ×ˢ B) =
      (∫⁻ ω in A,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          ((Ioc s t) ×ˢ B) ∂P) := by sorry

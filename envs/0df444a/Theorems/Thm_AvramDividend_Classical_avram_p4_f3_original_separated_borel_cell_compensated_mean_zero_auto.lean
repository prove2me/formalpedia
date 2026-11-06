-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_separated_borel_cell_compensated_mean_zero_auto
-- name    : AvramDividend.Classical.avram_p4_f3_original_separated_borel_cell_compensated_mean_zero_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:17:07.819836+00:00
-- url     : https://prove2.me/theorems/e3e7deac-be36-4ba5-b0b0-eadf7d258a3f
-- title:
--   Unconditional original-process separated Borel marked-cell mean-zero compensated count
-- statement:
--   Every physical marked-jump count of a spectrally negative Lévy process on (s,t] with marks in an arbitrary measurable negative Borel set B separated below −ε has an integrable compensated real-valued cell count whose expectation is zero. Both count integrability and finite Lévy rate follow from the actual original process and the separation hypothesis, with no auxiliary finiteness, conditional moments or equality in law assumed.
-- source:
--   Public Proved P2 separated original negative Borel rate finiteness, intrinsic marked count measurability, finite-nu count-real mean; and P4-S3 all-cell future original compensator rectangle 5933267b-b40f-483c-a57c-f63294dc12a8. Combine rate identity, integrable_toReal_of_lintegral_ne_top and probability-normalised integral subtraction. This supplies the original small/large compensated cell first-moment ingredient towards fdb9a6a3; quadratic/predictable and stopped-clock Itô obligations remain.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_future_negative_borel_rectangle_all_cells
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_mean
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_separated_borel_cell_compensated_mean_zero_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (N ω).toReal - r) P ∧
      (∫ ω, (N ω).toReal - r ∂P) = 0 := by sorry

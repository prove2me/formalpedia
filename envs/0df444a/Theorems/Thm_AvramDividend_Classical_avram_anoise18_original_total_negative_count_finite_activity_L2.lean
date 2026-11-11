-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
-- name    : AvramDividend.Classical.avram_anoise18_original_total_negative_count_finite_activity_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:27:08.054655+00:00
-- url     : https://prove2.me/theorems/a6562a4d-1b5a-4aa6-a604-e6a5dab88e68
-- title:
--   Original finite-activity all-negative jump count has uniform Poisson quadratic budget
-- statement:
--   For the original spectrally negative Lévy path, finite negative Lévy intensity implies the total number of negative physical jump marks in a finite interval has an integrable square and second moment at most the square of the physical Lévy rate plus that rate. The original count is obtained through genuine threshold-cutoff count exhaustion and Fatou from proved cutoff moment bounds, without any auxiliary process.
-- source:
--   Proved original finite-activity uniform negative cutoff count L2 d6906ce2 and exact all-negative count supremum 93b74ae6; original count finite almost surely ebd98fb4. The theorem is the missing finite-activity quadratic dominator for intrinsic Gaussian cutoff differences.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_uniform_count_L2
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_all_negative_marks_exhausted_by_threshold_bands
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_anoise18_original_total_negative_count_finite_activity_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))
    let R : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
    Integrable (fun ω => (N ω).toReal ^ 2) P ∧
      (∫ ω, (N ω).toReal ^ 2 ∂P) ≤ R ^ 2 + R := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
-- name    : AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:17:07.699193+00:00
-- url     : https://prove2.me/theorems/add050a6-3ff4-4747-9805-600b11b7b3d1
-- title:
--   Original intrinsic Borel marked jump count has stationary expected intensity under all deterministic shifts
-- statement:
--   For the actual original SpectrallyNegativeLevy process and any Borel mark cell, the expected literal source marked jump count on (s,s+T] equals that on (0,T]. No ν-rate identity, bounded variation or finite activity is assumed. Use the already Proved universal cadlag Borel jump-count extractor and literal same-path clock transport, then the original whole-future-kernel law against a constant past statistic. This reduces arbitrary-start Lévy–Itô mark-intensity identification to origin-start intervals without changing process or filtration.
-- source:
--   Original source universal cadlag count extractor 41bfd2c8, exact future-mark count transport b1721778, shifted cadlag source and genuine future kernel-past test avram_root29_01_original_future_kernel_past_test; all Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) := by sorry

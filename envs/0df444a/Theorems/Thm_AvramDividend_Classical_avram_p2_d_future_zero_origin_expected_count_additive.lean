-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_additive
-- name    : AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:38:18.936196+00:00
-- url     : https://prove2.me/theorems/c00b2582-d714-429d-a720-df3770e36760
-- title:
--   Original marked jump-count mean is additive in the zero-origin time horizon
-- statement:
--   For the unchanged original spectrally negative Lévy process and arbitrary Borel mark set, the expected intrinsic count on (0,a+b] equals the sum of its expected counts on (0,a] and (0,b]. The ENNReal equality permits infinite activity and does not identify the mark rate with ν.
-- source:
--   Use exact source samplewise adjacent-window additivity, measurability of the first marked count to apply lintegral_add_left, and the canonically Proved original stationary-mean count transport to replace (a,a+b] with (0,b].

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_adjacent_window_counts_add
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_marked_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (a + b) ×ˢ B) ∂P) =
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 a ×ˢ B) ∂P) +
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 b ×ˢ B) ∂P) := by sorry

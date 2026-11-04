-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_disjoint_borel_mark_mean_add
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_disjoint_borel_mark_mean_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:55:23.542723+00:00
-- url     : https://prove2.me/theorems/27cd2a24-6349-407b-9f94-b50025039ae2
-- title:
--   Expected original intrinsic jump count is additive across disjoint Borel marks
-- statement:
--   For the unchanged original spectrally negative Levy process on its original probability space and any two disjoint measurable jump-mark sets, the expected intrinsic count on the union of the two marks is the sum of their expected counts at the same nonnegative time horizon. This uses source count measurability and pathwise mark disjointness; no Levy rate or compensator is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_intrinsic_band_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_marked_rectangle_disjoint_mark_add

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_original_disjoint_borel_mark_mean_add {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : Disjoint B C) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (B ∪ C)) ∂P) =
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) +
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ C) ∂P) := by sorry

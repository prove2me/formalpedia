-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_marked_mean_iUnion_increasing_marks
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_iUnion_increasing_marks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:17:02.811438+00:00
-- url     : https://prove2.me/theorems/bf955e37-1c5c-413b-90e4-1a34210a2450
-- title:
--   Original intrinsic marked-jump expectation is continuous from below on increasing Borel marks
-- statement:
--   For the actual original spectrally negative Levy process, its ENNReal expected intrinsic jump count on an increasing union of measurable mark sets equals the supremum of expectations on the individual marked sets, at the original time interval (0,T]. This uses pathwise measure continuity, source measurability and monotone convergence only.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_intrinsic_band_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_increasing_borel_mark_rectangle_measure_iUnion

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_iUnion_increasing_marks {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hmono : Monotone B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (⋃ n, B n)) ∂P) =
    ⨆ n, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B n) ∂P) := by sorry

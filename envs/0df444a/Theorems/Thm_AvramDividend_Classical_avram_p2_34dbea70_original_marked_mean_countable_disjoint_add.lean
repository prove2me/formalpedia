-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_marked_mean_countable_disjoint_add
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_countable_disjoint_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:30:34.755063+00:00
-- url     : https://prove2.me/theorems/23013638-c709-4e55-b5cb-e4139f15a36f
-- title:
--   Countable additivity of the original intrinsic marked jump-count expectation
-- statement:
--   For any original spectrally negative Lévy process and pairwise disjoint Borel mark sets, the expectation of the exact intrinsic nonzero jump-counting measure of their union in a fixed finite time interval equals the sum of the individual expectations. No Lévy-rate or compensator assumption is required.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_intrinsic_band_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_disjoint_marked_rectangle_countable_add

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_countable_disjoint_add {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hDisj : Pairwise (Function.onFun Disjoint B)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (⋃ n, B n)) ∂P) =
    ∑' n, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B n) ∂P) := by sorry

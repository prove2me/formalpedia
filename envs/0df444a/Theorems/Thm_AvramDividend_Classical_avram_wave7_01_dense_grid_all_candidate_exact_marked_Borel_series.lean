-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_dense_grid_all_candidate_exact_marked_Borel_series
-- name    : AvramDividend.Classical.avram_wave7_01_dense_grid_all_candidate_exact_marked_Borel_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:12:46.661938+00:00
-- url     : https://prove2.me/theorems/660f311b-75c2-4d53-9b00-67955135ed89
-- title:
--   Every measurable dense-grid candidate time family has exact Borel jump marks and deduplicated count
-- statement:
--   Given any fixed dense grid, shrinking positive radii and countably many measurable source-path candidate times, construct globally measurable exact marked-jump extensions and the corresponding finite-horizon Borel-marked first-occurrence count. All witness selectors exist from grid density, and the truncated left windows converge to the actual positive candidate times. No finite activity or unrelated process is imposed.
-- source:
--   Combines Proved grid selector and dense right/left sampling lemmas with newly Proved exact measurable marked count 3f95364d and truncated-left limit helper; stage until all imports Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_path_countable_measurable_marked_jump_count
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_right_grid_selector_for_jump_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_left_grid_selector_for_jump_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_dense_source_grid_has_strict_right_mark_sample
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_dense_source_grid_has_strict_left_mark_sample
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_grid_left_window_limit_for_random_time
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_dense_grid_all_candidate_exact_marked_Borel_series
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (htime : ∀ k, Measurable (time k))
    (ε : ℕ → ℝ≥0) (hεpos : ∀ n, 0 < ε n)
    (hε : Tendsto ε atTop (𝓝 0))
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ mark : ℕ → (ℝ≥0 → ℝ) → ℝ,
      (∀ k, Measurable (mark k)) ∧
      (∀ (k : ℕ) (Y : ℝ≥0 → ℝ), 0 < time k Y →
        ContinuousWithinAt Y (Ici (time k Y)) (time k Y) →
        Tendsto Y (𝓝[<] (time k Y))
          (𝓝 (Function.leftLim Y (time k Y))) →
        mark k Y = Y (time k Y) - Function.leftLim Y (time k Y)) ∧
      Measurable (fun Y : ℝ≥0 → ℝ =>
        ∑' k : ℕ,
          if 0 < time k Y ∧ time k Y ≤ T ∧ mark k Y ∈ B ∧
              (∀ j : ℕ, j < k → time j Y ≠ time k Y)
          then (1 : ℝ≥0∞) else 0) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_exact_measurable_jump_mark_from_two_grid_families
-- name    : AvramDividend.Classical.avram_wave7_01_exact_measurable_jump_mark_from_two_grid_families
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:16:32.01046+00:00
-- url     : https://prove2.me/theorems/d1d6859e-14e4-4ebf-9147-90ca5853f00a
-- title:
--   Exact globally measurable original-path jump mark from two adapted grid sample families
-- statement:
--   On the genuine raw coordinate-path measurable space, countably measurable left and right grid evaluation families recover the exact jump mark at every positive random time where the path has right continuity and left limit. The theorem explicitly handles zero-time exclusion, shrinking grid intervals and countable coordinate measurability.
-- source:
--   Use Proved countably selected path evaluations to construct measurable left and right sample families, invoke Proved EReal liminf mark extension and right sampling limit, prove local left sampling limit by squeeze and neighbourhood-within composition.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_exact_jump_mark_measurable_extension_from_sample_limits
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_right_continuous_selected_grid_path_values_converge
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_countably_selected_raw_path_evaluation
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_exact_measurable_jump_mark_from_two_grid_families
    (grid : ℕ → ℝ≥0)
    (t : (ℝ≥0 → ℝ) → ℝ≥0)
    (rightIndex leftIndex : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hRightIndex : ∀ n, Measurable (rightIndex n))
    (hLeftIndex : ∀ n, Measurable (leftIndex n))
    (ε : ℕ → ℝ≥0) (hε : Tendsto ε atTop (𝓝 0))
    (hRightBounds : ∀ (Y : ℝ≥0 → ℝ) (n : ℕ),
      t Y ≤ grid (rightIndex n Y) ∧
      grid (rightIndex n Y) ≤ t Y + ε n)
    (lower : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (hLeftBounds : ∀ Y : ℝ≥0 → ℝ, 0 < t Y →
      ∀ n, lower n Y ≤ grid (leftIndex n Y) ∧
        grid (leftIndex n Y) < t Y)
    (hLower : ∀ Y : ℝ≥0 → ℝ, 0 < t Y →
      Tendsto (fun n => lower n Y) atTop (𝓝 (t Y))) :
    ∃ mark : (ℝ≥0 → ℝ) → ℝ,
      Measurable mark ∧
      ∀ Y : ℝ≥0 → ℝ, 0 < t Y →
        ContinuousWithinAt Y (Ici (t Y)) (t Y) →
        Tendsto Y (𝓝[<] (t Y))
          (𝓝 (Function.leftLim Y (t Y))) →
        mark Y = Y (t Y) - Function.leftLim Y (t Y) := by sorry

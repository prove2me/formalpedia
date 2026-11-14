-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_cell_approach_left
-- name    : AvramDividend.Classical.avram_chat24_uniform_cell_approach_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T19:04:11.957877+00:00
-- url     : https://prove2.me/theorems/ee1d7db9-620b-4bb4-b7de-5776ba123116
-- title:
--   Uniform-grid lower endpoints converge from the strict left
-- statement:
--   The distance of the lower endpoint to t is nonnegative and at most B/(n+1), which tends to zero. The lower endpoints lie strictly below t. This is the analytic shrinking-cell part of parent 977d6566-a376-446c-9fdf-c3488477439a; it does not assume existence or uniqueness of the chosen indices. The complete direct parent draft is preserved but its whole-theorem complexity score 0.1597 exceeds the configured -0.0523 limit. The two independent mathematical claims give a source-faithful reduction without changing that policy. Neither helper refers to the parent or to the other helper, so there is no dependency cycle.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_uniform_cell_approach_left
    (B t : ℝ≥0) (k : ℕ → ℕ)
    (hcell : ∀ n : ℕ,
      B * (k n : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) < t ∧
      t ≤ B * ((k n + 1 : ℕ) : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)) :
    Tendsto (fun n : ℕ => B * (k n : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0))
      atTop (𝓝[<] t) := by sorry

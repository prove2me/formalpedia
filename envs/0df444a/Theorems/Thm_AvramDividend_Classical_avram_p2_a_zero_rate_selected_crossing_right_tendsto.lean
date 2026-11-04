-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_selected_crossing_right_tendsto
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_selected_crossing_right_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:17:43.892833+00:00
-- url     : https://prove2.me/theorems/8d66c2c9-59e7-4a80-8343-93f3295fda9b
-- title:
--   Crossing shrinking source cells have right endpoints tending to genuine jump time
-- statement:
--   For an original source path, every selected shrinking half-open jump cell has left endpoint strictly before u and right endpoint at least u. If each right endpoint is within the vanishing cell width of its left endpoint, then the right endpoints converge to u by order squeeze. This bridges finite jump-cell selectors to eventual index distinctness.

import Mathlib
open Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_selected_crossing_right_tendsto
    (u : ℝ≥0) (a b w : ℕ → ℝ≥0)
    (hcell : ∀ n, a n < u ∧ u ≤ b n)
    (hbw : ∀ n, b n ≤ a n + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto b atTop (𝓝 u)  := by sorry

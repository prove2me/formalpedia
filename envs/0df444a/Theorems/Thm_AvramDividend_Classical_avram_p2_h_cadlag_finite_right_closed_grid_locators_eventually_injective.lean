-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_right_closed_grid_locators_eventually_injective
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_finite_right_closed_grid_locators_eventually_injective
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:02:28.502827+00:00
-- url     : https://prove2.me/theorems/4cd9be91-7a48-4ea5-9b0f-a88090688438
-- title:
--   Convergent right-closed grid endpoints give eventually injective jump-cell indices
-- statement:
--   For finitely many distinct actual jump times, if their assigned right-closed uniform-grid right endpoints tend to the corresponding time, their integer cell indices are eventually pairwise distinct. This avoids counting two jumps in one grid cell.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_distinct_time_endpoints_eventually_injective

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_finite_right_closed_grid_locators_eventually_injective
    (S : Finset ℝ≥0) (j : ℕ → ℝ≥0 → ℕ) (T : ℝ≥0)
    (hb : ∀ u ∈ S,
      Tendsto (fun n : ℕ =>
        (((j n u + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
        atTop (𝓝 u)) :
    ∀ᶠ n : ℕ in atTop,
      Set.InjOn (j n) (S : Set ℝ≥0) := by sorry

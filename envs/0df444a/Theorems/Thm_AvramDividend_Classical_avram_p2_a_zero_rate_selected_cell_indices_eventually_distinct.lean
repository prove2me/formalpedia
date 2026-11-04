-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_selected_cell_indices_eventually_distinct
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_selected_cell_indices_eventually_distinct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:26:10.381526+00:00
-- url     : https://prove2.me/theorems/e25dee56-668b-403b-8b3e-ad622e4e24ad
-- title:
--   Different genuine jump times have eventually distinct selected vanishing-mesh cells
-- statement:
--   Given two distinct actual jump times, each with a sequence of original uniform-mesh right endpoints converging to that time, prove their selected cell indices eventually differ. This is a deterministic Hausdorff separation step for matching finitely many genuine jumps injectively to uniform grid cells, without jump-rate or compensator assumptions.

import Mathlib
open Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_selected_cell_indices_eventually_distinct
    (u v : ℝ≥0) (huv : u ≠ v) (i j : ℕ → ℕ) (w : ℕ → ℝ≥0)
    (hi : Tendsto (fun n : ℕ =>
      ((i n + 1 : ℕ) : ℝ≥0) * w n) atTop (𝓝 u))
    (hj : Tendsto (fun n : ℕ =>
      ((j n + 1 : ℕ) : ℝ≥0) * w n) atTop (𝓝 v)) :
    ∀ᶠ n : ℕ in atTop, i n ≠ j n := by sorry

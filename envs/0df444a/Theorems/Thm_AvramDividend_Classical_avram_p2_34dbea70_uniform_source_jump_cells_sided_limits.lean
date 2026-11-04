-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_source_jump_cells_sided_limits
-- name    : AvramDividend.Classical.avram_p2_34dbea70_uniform_source_jump_cells_sided_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:31:23.287744+00:00
-- url     : https://prove2.me/theorems/38461770-4053-43bc-b84a-70b3f4c6a8c3
-- title:
--   Every positive source jump has valid shrinking uniform right-closed cells
-- statement:
--   For each u in (0,T] and strictly positive T, choose the exact uniform right-closed cell index i_n≤n from the existing Proved locator. Its left and right endpoints straddle u and converge towards u from the strict-left and weak-right sides respectively, since their actual cell widths T/(n+1) tend to zero. This is the missing explicit grid instantiation of the source jump detector and does not use probabilistic or compensator assumptions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_halfopen_cell_locator
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_vanishing_width_halfopen_endpoints

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_uniform_source_jump_cells_sided_limits
    (T u : ℝ≥0) (hT : 0 < T) (hu : 0 < u) (huT : u ≤ T) :
    ∃ i : ℕ → ℕ,
      (∀ n, i n ≤ n ∧
        (i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
        u ≤ ((i n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∧
      Tendsto (fun n => (i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))
        atTop (𝓝[<] u) ∧
      Tendsto (fun n => ((i n + 1 : ℕ) : ℝ≥0) *
        (T / ((n : ℝ≥0) + 1))) atTop (nhdsWithin u (Ici u)) := by sorry

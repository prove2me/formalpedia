-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_infinite_t3_grid_nodes_strictly_before_terminal
-- name    : AvramDividend.Classical.avram_route_infinite_t3_grid_nodes_strictly_before_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:01:12.295499+00:00
-- url     : https://prove2.me/theorems/81f7c2ca-53d3-4eb3-a8e6-0cb5aab53940
-- title:
--   Original BV uniform physical-grid nodes precede the terminal horizon strictly
-- statement:
--   For the original uniform physical grid u(n,i) = T i/(n+2) with positive horizon T, all nodes i through n+1 are strictly earlier than T. In particular the final grid point leaves the strict right-horizon interval needed for source-exact ruin/contact atom accounting.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_infinite_t3_grid_nodes_strictly_before_terminal
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ n i, i ≤ n + 1 →
      u n i < (⟨T, le_of_lt hT⟩ : ℝ≥0) := by sorry

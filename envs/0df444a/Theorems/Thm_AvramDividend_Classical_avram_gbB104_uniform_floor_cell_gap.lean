-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB104_uniform_floor_cell_gap
-- name    : AvramDividend.Classical.avram_gbB104_uniform_floor_cell_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:34:48.156632+00:00
-- url     : https://prove2.me/theorems/e6149807-d695-4ed9-a6cd-ab7a98d00f5a
-- title:
--   Exact floor-selected uniform grid left endpoint lies within one cell of time
-- statement:
--   With the original positive integer horizon and m+1 uniform partitions, the floor-selected left grid endpoint is at or before any nonnegative time and has discrepancy at most one grid cell length. This is the deterministic mesh-index estimate used to prove original postpayment grid step convergence in B102.

import Mathlib
open Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB104_uniform_floor_cell_gap
    (n m : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
    let i : ℕ := ⌊t / Δ⌋₊
    ((i : ℝ) * Δ ≤ t) ∧
      t - (i : ℝ) * Δ ≤ Δ := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB257_monotone_grid_large_dividend_cell_count_bound
-- name    : AvramDividend.Classical.avram_gbB257_monotone_grid_large_dividend_cell_count_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T15:48:42.340954+00:00
-- url     : https://prove2.me/theorems/8d081cd7-afc1-4d56-a6b6-16f15ae54e9e
-- title:
--   Monotone dividend grid has at most total variation divided by threshold many large-increment cells
-- statement:
--   For a real monotone sequence sampled on a finite physical-time grid, the number of grid cells on which the dividend increases by more than epsilon, multiplied by epsilon, is bounded by total dividend variation across the grid. This is the deterministic bad-cell-count estimate used to control occupation at a prescribed interior level for the original adapted Gaussian dividend process in Avram B100.

import Mathlib
open Finset
noncomputable section

theorem AvramDividend.Classical.avram_gbB257_monotone_grid_large_dividend_cell_count_bound
    (d : ℕ → ℝ) (hd : Monotone d) (epsilon : ℝ) (hEps : 0 < epsilon)
    (n : ℕ) :
    (((Finset.range n).filter (fun i => epsilon < d (i + 1) - d i)).card : ℝ) *
      epsilon ≤ d n - d 0 := by sorry

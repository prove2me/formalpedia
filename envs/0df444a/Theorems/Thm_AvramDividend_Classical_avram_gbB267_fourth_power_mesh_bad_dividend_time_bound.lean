-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB267_fourth_power_mesh_bad_dividend_time_bound
-- name    : AvramDividend.Classical.avram_gbB267_fourth_power_mesh_bad_dividend_time_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:34:28.112218+00:00
-- url     : https://prove2.me/theorems/2bb3a270-fc25-435b-9641-ab2f1f81dc0d
-- title:
--   Fourth-power physical grid and cubic threshold give inverse-refinement bad-dividend time bound
-- statement:
--   For any real monotone dividend sequence sampled on a physical grid with n times m to the fourth cells and goodness threshold the reciprocal of m cubed, the time length of all large-dividend cells is bounded by the total dividend variation divided by m. The result is a precise rational-rate specialisation of the already Proved monotone bad-cell count B257 and is directly applicable to the source-faithful zero-jump Gaussian finite-cap fixed-level occupation time-grid argument B100.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB257_monotone_grid_large_dividend_cell_count_bound

open Finset AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB267_fourth_power_mesh_bad_dividend_time_bound
    (d : ℕ → ℝ) (hd : Monotone d)
    (m n : ℕ) (hm : 0 < m) :
    (((Finset.range (n * m ^ 4)).filter
      (fun i => 1 / ((m : ℝ) ^ 3) < d (i + 1) - d i)).card : ℝ) *
      (1 / ((m : ℝ) ^ 4)) ≤
    (d (n * m ^ 4) - d 0) / (m : ℝ) := by sorry

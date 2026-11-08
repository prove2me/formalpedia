-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_admissible_nonrefining_physical_grid
-- name    : AvramDividend.Classical.avram_bv_residual9_admissible_nonrefining_physical_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:26:09.151206+00:00
-- url     : https://prove2.me/theorems/83640395-d4b3-47a3-a30f-7f83642acdd1
-- title:
--   The original physical-grid endpoint and monotonicity conditions permit a nonrefining first interval
-- statement:
--   The exact original hgrid and hmono conditions at horizon T=1 admit a monotone grid in which all positive indices occupy the same point 1−1/(n+2). Its first cell remains at least one half for every n, so endpoint convergence and monotonicity do not force mesh refinement.
-- source:
--   AVRAM BV-RESIDUAL9 round-three explicit grid diagnostic

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_admissible_nonrefining_physical_grid :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n : ℕ, u n 0 = 0 ∧
        ((u n (n + 1) : ℝ) = 1 - 1 / ((n : ℝ) + 2))) ∧
      (∀ (n i : ℕ), i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n : ℕ, (1 / 2 : ℝ) ≤ (u n 1 : ℝ)) := by sorry

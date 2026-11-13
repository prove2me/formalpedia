-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a27_prehorizon_grid_le
-- name    : AvramDividend.Classical.avram_ga_a27_prehorizon_grid_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:40:24.686195+00:00
-- url     : https://prove2.me/theorems/6f6b6210-657a-4e52-ad44-d014b75b3451
-- title:
--   Penultimate Gaussian clipped-grid point is no later than the horizon
-- statement:
--   Every left endpoint m*n/(m+1) lies in the compact time interval [0,n]. Together with the deterministic mesh limit and almost-sure uniform continuity of the original sample path, this supplies the exact hypotheses for final Brownian increment convergence.
-- source:
--   Avram Gaussian A27 original path bounded mesh

import Mathlib
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_a27_prehorizon_grid_le (n : ℝ≥0) (m : ℕ) :
    (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1)) ≤ n := by sorry

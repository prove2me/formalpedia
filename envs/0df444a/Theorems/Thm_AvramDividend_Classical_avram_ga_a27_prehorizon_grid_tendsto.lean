-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a27_prehorizon_grid_tendsto
-- name    : AvramDividend.Classical.avram_ga_a27_prehorizon_grid_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:38:00.99691+00:00
-- url     : https://prove2.me/theorems/f2239370-84c8-468d-b706-271dac3cdae0
-- title:
--   Penultimate Gaussian mesh time tends to the finite stopping horizon in NNReal
-- statement:
--   The left endpoint m*n/(m+1) of the terminal Gaussian cell tends to the finite horizon n as m grows. This combines with almost-sure uniform continuity of the original zero-jump Levy path to make the last Gaussian increment vanish on horizon-boundary paths.
-- source:
--   Avram Gaussian A27 deterministic prehorizon convergence

import Mathlib
open Filter
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_a27_prehorizon_grid_tendsto (n : ℝ≥0) :
    Tendsto (fun m : ℕ => (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1)))
      atTop (nhds n) := by sorry

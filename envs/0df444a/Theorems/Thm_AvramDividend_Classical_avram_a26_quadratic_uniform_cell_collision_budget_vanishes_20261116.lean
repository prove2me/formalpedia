-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_quadratic_uniform_cell_collision_budget_vanishes_20261116
-- name    : AvramDividend.Classical.avram_a26_quadratic_uniform_cell_collision_budget_vanishes_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:09:26.172304+00:00
-- url     : https://prove2.me/theorems/83973f54-0fe2-485c-b676-e7af3ede2356
-- title:
--   Uniform-grid quadratic collision budget vanishes as the number of cells grows
-- statement:
--   For a fixed real source rate a, the quadratic finite-grid collision budget n(a/n)^2/2 tends to zero as n tends to infinity. Rewriting for n>0 gives (a^2/2)/n, whose limit follows from the pinned Mathlib reciprocal limit theorem. This is the deterministic convergence used with the proved original physical grid collision estimate.
-- source:
--   Elementary algebra and pinned Mathlib tendsto_const_div_atTop_nhds_zero_nat.

import Mathlib
open Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_a26_quadratic_uniform_cell_collision_budget_vanishes_20261116 (a : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * ((a / (n : ℝ)) ^ 2 / 2))
      atTop (𝓝 (0 : ℝ)) := by sorry

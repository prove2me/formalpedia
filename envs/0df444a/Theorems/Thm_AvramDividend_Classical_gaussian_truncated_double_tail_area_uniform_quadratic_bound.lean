-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_truncated_double_tail_area_uniform_quadratic_bound
-- name    : AvramDividend.Classical.gaussian_truncated_double_tail_area_uniform_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T11:44:33.385464+00:00
-- url     : https://prove2.me/theorems/4f553bf7-72f1-4982-832d-b81cc746e2cc
-- title:
--   Uniform quadratic domination of every truncated Gaussian double-tail area
-- statement:
--   The Gaussian double-tail truncated area z min(R,z)−min(R,z)²/2 is bounded above by z²/2 for every real R,z. The nonnegative difference is (z−min(R,z))²/2. Unlike the previously proved local area bound with an R-dependent constant, this is uniform in R and, when combined with Esscher weighted-second-moment integrability, supplies the global L1 kernel estimate.
-- source:
--   Elementary square-completion inequality. Strengthens the Proved gaussian_truncated_double_tail_area_bound 07a276b0-dbdf-4a23-b256-047458266833.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem AvramDividend.Classical.gaussian_truncated_double_tail_area_uniform_quadratic_bound (R z : ℝ) :
    z * min R z - (min R z) ^ 2 / 2 ≤ z ^ 2 / 2 := by sorry

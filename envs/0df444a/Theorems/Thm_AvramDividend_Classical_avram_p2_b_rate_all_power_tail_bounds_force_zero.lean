-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_all_power_tail_bounds_force_zero
-- name    : AvramDividend.Classical.avram_p2_b_rate_all_power_tail_bounds_force_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:54:52.984955+00:00
-- url     : https://prove2.me/theorems/8b518308-e1a6-4ea6-acc8-622aac99145a
-- title:
--   Uniform exponential power tail bounds force mass to vanish
-- statement:
--   For a strictly superunit threshold R, any nonnegative mass a satisfying R^k*a <= C for every natural k and one common finite real C must vanish. This is the exact deterministic final step that excludes positive jumps from weighted small-time image measures when the negative Levy moments are uniformly bounded; it assumes no stochastic rate.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.OrderClosed

open Filter Topology

theorem AvramDividend.Classical.avram_p2_b_rate_all_power_tail_bounds_force_zero
    (R a C : ℝ) (hR : 1 < R) (ha : 0 ≤ a)
    (hbound : ∀ k : ℕ, R ^ k * a ≤ C) : a = 0 := by sorry

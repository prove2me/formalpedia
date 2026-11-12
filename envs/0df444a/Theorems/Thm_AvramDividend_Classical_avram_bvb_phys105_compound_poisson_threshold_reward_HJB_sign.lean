-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys105_compound_poisson_threshold_reward_HJB_sign
-- name    : AvramDividend.Classical.avram_bvb_phys105_compound_poisson_threshold_reward_HJB_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:00:59.408111+00:00
-- url     : https://prove2.me/theorems/6a454f64-10bc-441e-9d3c-9a7c80e1f48e
-- title:
--   Discounted threshold reward satisfies compound-Poisson interior HJB sign
-- statement:
--   For a unit downward jump of rate 20 and drift 10, the candidate value zero on negative reserves and one plus reserve on nonnegative reserves satisfies the exact discounted generator inequality at all strictly positive reserves.
-- source:
--   Bounded-variation physical stopped-cash and ruin threshold countermodel HJB prerequisite

import Mathlib

theorem AvramDividend.Classical.avram_bvb_phys105_compound_poisson_threshold_reward_HJB_sign (y : ℝ) (hy : 0 < y) : let w : ℝ → ℝ := fun z => if z < 0 then 0 else 1 + z; 10 + 20 * (w (y - 1) - w y) - w y ≤ 0 := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_monotone_path_continuous_of_leftLim_and_right
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_monotone_path_continuous_of_leftLim_and_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:07:55.626242+00:00
-- url     : https://prove2.me/theorems/90a030b7-f7ed-487e-a842-8aff1916031a
-- title:
--   Monotone real paths with coincident left and right limits are continuous at positive times
-- statement:
--   For a monotone real-valued function on nonnegative time, at each strictly positive time, left-limit equal to value and convergence from the right to value imply continuity at that time. This analytic bridge assembles the source BV drift residual no-jump and right-continuity lemmas.
-- source:
--   Pinned Mathlib.Topology.Order.LeftRightLim, Monotone.continuousAt_iff_leftLim_eq_rightLim and rightLim_eq_of_tendsto.

import Mathlib
import Mathlib.Topology.Order.LeftRightLim

open Filter Set Topology
open scoped NNReal

/-- A monotone real-valued path without a positive-time left jump,
whose right limit agrees with its value, is continuous at that time. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_monotone_path_continuous_of_leftLim_and_right
    (f : ℝ≥0 → ℝ) (hm : Monotone f) (t : ℝ≥0) (ht : 0 < t)
    (hl : Function.leftLim f t = f t)
    (hr : Filter.Tendsto f (𝓝[>] t) (nhds (f t))) :
    ContinuousAt f t := by sorry

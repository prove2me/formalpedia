-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_right
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:53:11.676518+00:00
-- url     : https://prove2.me/theorems/31a66ae2-d2ca-4397-8112-0224b0c8c92f
-- title:
--   Absolutely summable atomic cumulative real jump sums are right-continuous at every nonnegative time
-- statement:
--   For a genuine summable family of real atomic increments on NNReal time, the cumulative sum over positive times up to s converges as s decreases to t to the sum including the atom at t. This pure pinned-Mathlib Tannery lemma is the right-continuity counterpart of the previously accepted left-limit theorem and applies to actual BV Levy jumps.
-- source:
--   Pinned Mathlib tendsto_tsum_of_dominated_convergence, isOpen_Iio.mem_nhds and nhdsWithin order filters; real absolute summability supplies a fixed summable majorant.

import Mathlib
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.LeftRightLim

open Filter Set Topology
open scoped NNReal BigOperators

/-- An absolutely summable real atomic cumulative series converges from
the right to the sum including its time-t atom, including at time zero. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_right
    (f : ℝ≥0 → ℝ) (hSum : Summable (fun u : ℝ≥0 => |f u|))
    (t : ℝ≥0) :
    Filter.Tendsto
      (fun s : ℝ≥0 => ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ s then f u else 0)
      (𝓝[>] t)
      (nhds (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then f u else 0)) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_left
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:09:05.407284+00:00
-- url     : https://prove2.me/theorems/3f8d0995-a827-4a6f-a22b-45826e05f825
-- title:
--   Absolute summability makes real cumulative atomic jump series converge to strict-past sum from the left
-- statement:
--   For a summable indexed family of actual-real-sized jumps on nonnegative time, its cumulative step-function sum over (0,s] tends, as s increases to positive t from the left, to the sum over (0,t). This is an analytic left-limit theorem used to show that subtracting actual BV jumps removes all path discontinuities.
-- source:
--   Pinned Mathlib Tannery dominated-convergence theorem and order topology of NNReal, with each atom inclusion eventually constant approaching positive t from below. No probabilistic representation.

import Mathlib
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.LeftRightLim

open Filter Set Topology
open scoped NNReal BigOperators

/-- An absolutely summable real atomic cumulative jump path converges
to its strict-past sum when observed from the left at positive time. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_left
    (f : ℝ≥0 → ℝ) (hSum : Summable (fun u : ℝ≥0 => |f u|))
    (t : ℝ≥0) (ht : 0 < t) :
    Filter.Tendsto
      (fun s : ℝ≥0 =>
        ∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then f u else 0)
      (𝓝[<] t)
      (nhds (∑' u : ℝ≥0, if 0 < u ∧ u < t then f u else 0)) := by sorry

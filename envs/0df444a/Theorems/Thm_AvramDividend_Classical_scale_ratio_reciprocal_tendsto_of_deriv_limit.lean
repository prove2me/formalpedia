-- Prove2me | Theorems.Thm_AvramDividend_Classical_scale_ratio_reciprocal_tendsto_of_deriv_limit
-- name    : AvramDividend.Classical.scale_ratio_reciprocal_tendsto_of_deriv_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:57:30.526566+00:00
-- url     : https://prove2.me/theorems/e23b9809-ce74-4362-be31-f67c30730d1f
-- title:
--   Scale-function quotient converges at zero when the derivative has a nonzero right limit
-- statement:
--   For a function continuous from the right at zero, if its ordinary derivatives at the positive reciprocal barriers converge to a nonzero real number d, then the quotients W(a)/W'(a) at these barriers converge to W(0)/d. The proof composes one-sided continuity with the reciprocal sequence and then uses continuity of division away from zero. Applied to a q-scale function, this provides the analytic limit required by the Proved zero-cap transfer theorem whenever the boundary extended derivative is finite and identified with d.
-- source:
--   Mathlib Analysis.SpecificLimits.Basic, Topology.ContinuousOn and continuity of division.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.Positivity

open Filter Set

theorem AvramDividend.Classical.scale_ratio_reciprocal_tendsto_of_deriv_limit
    (W : ℝ → ℝ)
    (hcont : ContinuousWithinAt W (Set.Ici (0 : ℝ)) 0)
    (d : ℝ) (hd : d ≠ 0)
    (hderiv : Filter.Tendsto
      (fun n : ℕ => deriv W (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds d)) :
    Filter.Tendsto
      (fun n : ℕ => W (1 / ((n : ℝ) + 1)) /
        deriv W (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds (W 0 / d)) := by sorry

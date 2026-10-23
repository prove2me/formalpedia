-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_monotoneOn_bounded_tendsto_positive
-- name    : AvramDividend.Classical.positive_monotoneOn_bounded_tendsto_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:28:13.008844+00:00
-- url     : https://prove2.me/theorems/5474a6a8-5fce-4ac2-8c3b-fc638acabdcb
-- title:
--   Positive bounded increasing functions on the positive axis converge to positive finite limits
-- statement:
--   Let V be strictly positive and nondecreasing on (0,infinity), and suppose there is a finite constant C such that V(x)<=C for all x>0. Then there exists L>0 such that V(x) tends to L as x tends to +infinity. Extend the function to a monotone real-line function by clamping its argument from below at 1; apply the Mathlib monotone convergence theorem and rule out divergence using the uniform upper bound. Positivity of the limit follows from a fixed positive value V(1). This packages the analytic step needed immediately above the Esscher monotone bounded scale-function target.

import Mathlib.Topology.Order.MonotoneConvergence
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter Set
open scoped Topology

theorem AvramDividend.Classical.positive_monotoneOn_bounded_tendsto_positive
    (V : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hmono : MonotoneOn V (Ioi (0 : ℝ)))
    (hupper : ∃ C : ℝ, ∀ x : ℝ, 0 < x → V x ≤ C) :
    ∃ L : ℝ, 0 < L ∧ Tendsto V atTop (𝓝 L) := by sorry

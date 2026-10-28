-- Prove2me | Theorems.Thm_AvramDividend_Classical_stationary_piecewise_hasDerivAt_zero
-- name    : AvramDividend.Classical.stationary_piecewise_hasDerivAt_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:59:41.485537+00:00
-- url     : https://prove2.me/theorems/6521a4cb-167c-4de5-a04a-c0d2f72b898f
-- title:
--   Differentiable pasting at a stationary barrier join
-- statement:
--   Deterministic smooth-fit at a stationary boundary. Given a real differentiable left branch with zero derivative at c and value v, joining it to the constant value v on the right yields ordinary derivative zero at c. This is the exact local calculus bridge required to differentiate the Gaussian scale-derivative profile at the optimal barrier, using W''(c*)=0.
-- source:
--   Avram, Palmowski and Pistorius (2007), smooth-fit at c*: W''(c*)=0; elementary gluing of one-sided derivatives.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Piecewise
open Set Topology

namespace AvramDividend.Classical
/-- If a left branch has zero derivative and matches a constant right branch, the paste has zero derivative at the join. -/
theorem stationary_piecewise_hasDerivAt_zero
    (f : ℝ → ℝ) (c v : ℝ)
    (hdiff : DifferentiableAt ℝ f c)
    (hflat : deriv f c = 0)
    (hmatch : f c = v) :
    HasDerivAt ((Iic c).piecewise f (fun _ : ℝ => v)) 0 c := by
  sorry
end AvramDividend.Classical

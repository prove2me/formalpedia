-- Prove2me | Theorems.Thm_D1Bound5_ordinary_integer_orders_log_bound
-- name    : D1Bound5.ordinary_integer_orders_log_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:25:11.089526+00:00
-- url     : https://prove2.me/theorems/ec437723-9bd6-4f49-b3b4-9c5631aa975d
-- title:
--   Ordinary integer orders log bound
-- statement:
--   Selecting the actual positive integer order from the logarithmic floor gives a division-free logarithmic inequality. This is the scalar step from all integer orders to the ordinary height envelope.
-- source:
--   D1Bound5/OrdinaryHeightScalar.lean, lines 7-54, SHA-256 0823b901aedbcca1a333b2b988ab8e6173c80406182e7af0372435df321e588d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

section
namespace D1Bound5


theorem _root_.D1Bound5.ordinary_integer_orders_log_bound (H R Z X : ℝ)
    (hH : 1 ≤ H) (hR : 1 < R) (hZ : 1 ≤ Z) (hX : 0 < X)
    (horders : ∀ k : ℕ, 1 ≤ k → 1 < X*H^k/Z+Z/(2*R^k)) :
    Real.log Z*(Real.log R-Real.log H) < Real.log (2*X*H)*Real.log R := by sorry





end D1Bound5
end

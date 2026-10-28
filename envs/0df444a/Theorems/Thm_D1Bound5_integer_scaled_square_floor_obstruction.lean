-- Prove2me | Theorems.Thm_D1Bound5_integer_scaled_square_floor_obstruction
-- name    : D1Bound5.integer_scaled_square_floor_obstruction
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:36:25.732873+00:00
-- url     : https://prove2.me/theorems/3f071507-1548-4b4a-b55b-5e0072f53430
-- title:
--   Integer scaled square floor obstruction
-- statement:
--   The same obstruction after multiplication by a positive integer. No divisibility hypothesis or integer division is required.
-- source:
--   D1Bound5/QuadSquareFloorObstruction.lean, lines 18-27, SHA-256 189bc6919f96623fb014a3f2f03e165069f8dce0da25caec94ef0406cc2c9b3e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith

section
namespace D1Bound5




theorem _root_.D1Bound5.integer_scaled_square_floor_obstruction {scale m k : ℤ}
    (hscale : 0 < scale) (hk : 0 ≤ k)
    (hlo : scale * k ^ 2 < m) (hhi : m < scale * (k + 1) ^ 2) :
    ¬ ∃ n : ℤ, m = scale * n ^ 2 := by sorry







namespace QuadInt









end QuadInt
end D1Bound5
end

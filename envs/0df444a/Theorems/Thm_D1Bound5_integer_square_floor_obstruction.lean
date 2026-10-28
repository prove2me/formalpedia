-- Prove2me | Theorems.Thm_D1Bound5_integer_square_floor_obstruction
-- name    : D1Bound5.integer_square_floor_obstruction
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:10.184262+00:00
-- url     : https://prove2.me/theorems/a37d5975-c6d3-4fbd-9bb8-0eae229a1b4c
-- title:
--   Integer square floor obstruction
-- statement:
--   An integer strictly between consecutive nonnegative integer squares cannot itself be a square. The witness is checked by integer arithmetic.
-- source:
--   D1Bound5/QuadSquareFloorObstruction.lean, lines 6-16, SHA-256 189bc6919f96623fb014a3f2f03e165069f8dce0da25caec94ef0406cc2c9b3e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith

section
namespace D1Bound5


theorem _root_.D1Bound5.integer_square_floor_obstruction {m k : ℤ}
    (hk : 0 ≤ k) (hlo : k ^ 2 < m) (hhi : m < (k + 1) ^ 2) :
    ¬ ∃ n : ℤ, m = n ^ 2 := by sorry









namespace QuadInt









end QuadInt
end D1Bound5
end

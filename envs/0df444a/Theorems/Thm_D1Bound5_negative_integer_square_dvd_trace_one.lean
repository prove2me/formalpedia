-- Prove2me | Theorems.Thm_D1Bound5_negative_integer_square_dvd_trace_one
-- name    : D1Bound5.negative_integer_square_dvd_trace_one
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:15:50.127258+00:00
-- url     : https://prove2.me/theorems/990b2caa-e056-40b8-915d-676fd29b13b2
-- title:
--   Negative integer square dvd trace one
-- statement:
--   In the trace-one model, a negative rational integer square has real coordinate divisible by 4*nu-1. No positivity assumption on this parameter is required for the necessary divisibility condition.
-- source:
--   D1Bound5/PairNegativeIntegerObstruction.lean, lines 28-40, SHA-256 099be79d73801fcfb76bdc30024dc74b43ab6bdb2e935fcd75d8e115af902e02. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5






theorem _root_.D1Bound5.negative_integer_square_dvd_trace_one {nu : ℤ}
    (z : QuadInt 1 nu) (him : z.im = 0) (hre : z.re < 0)
    (hsquare : ∃ r : QuadInt 1 nu, r * r = z) : (4 * nu - 1) ∣ z.re := by sorry





end D1Bound5
end

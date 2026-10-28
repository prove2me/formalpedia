-- Prove2me | Theorems.Thm_D1Bound5_QuadInt_floorObstructionBool_sound
-- name    : D1Bound5.QuadInt.floorObstructionBool_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:50.252979+00:00
-- url     : https://prove2.me/theorems/2c8f75bb-57a5-4a11-b4f9-c12ff9da891f
-- title:
--   Quad Int — floor Obstruction Bool sound
-- statement:
--   Soundness of the inexpensive floor-witness checker. It uses the accepted rational-square classification and multiplicativity of norm; no candidate square root is computed.
-- source:
--   D1Bound5/QuadSquareFloorObstruction.lean, lines 103-149, SHA-256 189bc6919f96623fb014a3f2f03e165069f8dce0da25caec94ef0406cc2c9b3e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_QuadSquareFloorObstruction_Definitions

section
namespace D1Bound5











namespace QuadInt








theorem _root_.D1Bound5.QuadInt.floorObstructionBool_sound {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) {z : QuadInt tau nu} {k : ℕ}
    (h : floorObstructionBool z k = true) :
    ¬ ∃ r : QuadInt tau nu, r * r = z := by sorry

end QuadInt
end D1Bound5
end

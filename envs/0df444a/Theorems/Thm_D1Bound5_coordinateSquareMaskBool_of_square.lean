-- Prove2me | Theorems.Thm_D1Bound5_coordinateSquareMaskBool_of_square
-- name    : D1Bound5.coordinateSquareMaskBool_of_square
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:40.225895+00:00
-- url     : https://prove2.me/theorems/5e9a6ea4-6558-4929-96f2-d7045eee16f5
-- title:
--   Coordinate Square Mask Bool of square
-- statement:
--   Reduction of an actual integral square is accepted by a valid finite mask. No primality, positive discriminant or nonzero-root hypothesis is needed.
-- source:
--   D1Bound5/FastSquareTest.lean, lines 25-35, SHA-256 93fb33ff431ce54869bd6adeaf8ad3dbc69d1bda6af9b19b16adf05480dbef74. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions

section
namespace D1Bound5
open QuadInt








theorem _root_.D1Bound5.coordinateSquareMaskBool_of_square {tau nu : ℤ}
    (k mask : ℕ) (htable : CoordinateSquareMaskValid tau nu k mask)
    (z r : QuadInt tau nu) (hr : r*r = z) :
    coordinateSquareMaskBool k mask z = true := by sorry













end D1Bound5
end

-- Prove2me | Theorems.Thm_D1Bound5_hasSquareRootFast_iff
-- name    : D1Bound5.hasSquareRootFast_iff
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:36:24.4446+00:00
-- url     : https://prove2.me/theorems/e78cd1b3-c80d-45bb-b8c4-2179241af614
-- title:
--   Has Square Root Fast iff
-- statement:
--   Auxiliary result `hasSquareRootFast_iff` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FastSquareTest.lean, lines 64-74, SHA-256 93fb33ff431ce54869bd6adeaf8ad3dbc69d1bda6af9b19b16adf05480dbef74. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions

section
namespace D1Bound5
open QuadInt



















theorem _root_.D1Bound5.hasSquareRootFast_iff {tau nu : ℤ}
    (hd : 0 < discriminant tau nu)
    (sieve : List (ℕ × ℕ)) (hvalid : CoordinateSquareSieveValid tau nu sieve)
    (z : QuadInt tau nu) : hasSquareRootFast sieve z = true ↔ ∃ r, r*r = z := by sorry

end D1Bound5
end

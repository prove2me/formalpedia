-- Prove2me | Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
-- name    : D1Bound5.QuadInt.hasSquareRoot_iff
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:38:13.502101+00:00
-- url     : https://prove2.me/theorems/9c0661c6-a519-4d21-9406-dd838059ab10
-- title:
--   Quad Int — has Square Root iff
-- statement:
--   The checker is necessary and sufficient, not merely a source of positive witnesses or a one-sided modular obstruction.
-- source:
--   D1Bound5/SquareTest.lean, lines 117-130, SHA-256 adcc13a33378056841f44d21785e69909232e4def68eb73ca742e5a49ce15ac3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions

section
namespace D1Bound5.QuadInt

variable {tau nu : ℤ}


















theorem _root_.D1Bound5.QuadInt.hasSquareRoot_iff (hd : 0 < discriminant tau nu) (z : QuadInt tau nu) :
    hasSquareRoot z = true ↔ ∃ r : QuadInt tau nu, r*r = z := by sorry







end D1Bound5.QuadInt
end

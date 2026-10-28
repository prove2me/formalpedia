-- Prove2me | Theorems.Thm_D1Bound5_QuadInt_exists_normalized_root
-- name    : D1Bound5.QuadInt.exists_normalized_root
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:22:44.191152+00:00
-- url     : https://prove2.me/theorems/1cdefc58-782d-4081-bbea-439fd70f8d77
-- title:
--   Quad Int — exists normalized root
-- statement:
--   A square root can be given nonnegative doubled real part; if that part is zero, its second coordinate may also be chosen nonnegative.
-- source:
--   D1Bound5/SquareTest.lean, lines 18-41, SHA-256 adcc13a33378056841f44d21785e69909232e4def68eb73ca742e5a49ce15ac3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5.QuadInt

variable {tau nu : ℤ}




theorem _root_.D1Bound5.QuadInt.exists_normalized_root {z : QuadInt tau nu} (hz : ∃ r, r*r = z) :
    ∃ r : QuadInt tau nu, r*r = z ∧ 0 ≤ 2*r.re+tau*r.im ∧
      (2*r.re+tau*r.im = 0 → 0 ≤ r.im) := by sorry





















end D1Bound5.QuadInt
end

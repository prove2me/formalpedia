-- Prove2me | Theorems.Thm_D1Bound5_QuadInt_four_norm
-- name    : D1Bound5.QuadInt.four_norm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:58:40.135005+00:00
-- url     : https://prove2.me/theorems/61b112c1-2801-4108-977c-312534554c2d
-- title:
--   Quad Int — four norm
-- statement:
--   Equation (integrated-disk), completed-square identity.
-- source:
--   D1Bound5/Coordinates.lean, lines 23-28, SHA-256 da0cb0c42a6044e813dcdaaa1831735e6baddba8fa16b037f5289e53bcfae065. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5



namespace QuadInt

variable {tau nu : ℤ}






theorem _root_.D1Bound5.QuadInt.four_norm (z : QuadInt tau nu) :
    4*z.norm = (2*z.re+tau*z.im)^2 + discriminant tau nu*z.im^2 := by sorry











end QuadInt
end D1Bound5
end

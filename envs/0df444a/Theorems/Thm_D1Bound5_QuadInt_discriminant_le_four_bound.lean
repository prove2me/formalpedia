-- Prove2me | Theorems.Thm_D1Bound5_QuadInt_discriminant_le_four_bound
-- name    : D1Bound5.QuadInt.discriminant_le_four_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:53:43.711086+00:00
-- url     : https://prove2.me/theorems/46b31ddc-b44d-4fcd-9c85-bf2383b2e6ba
-- title:
--   Quad Int — discriminant le four bound
-- statement:
--   A nonreal element in a bounded disk bounds the field discriminant. Used for the Delta<=60 reduction in lem:tail-irregular.
-- source:
--   D1Bound5/Coordinates.lean, lines 64-73, SHA-256 da0cb0c42a6044e813dcdaaa1831735e6baddba8fa16b037f5289e53bcfae065. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5



namespace QuadInt

variable {tau nu : ℤ}
















theorem _root_.D1Bound5.QuadInt.discriminant_le_four_bound (hd : 0 < discriminant tau nu)
    {z : QuadInt tau nu} {M : ℤ} (hM : z.norm ≤ M) (hy : z.im ≠ 0) :
    discriminant tau nu ≤ 4*M := by sorry

end QuadInt
end D1Bound5
end

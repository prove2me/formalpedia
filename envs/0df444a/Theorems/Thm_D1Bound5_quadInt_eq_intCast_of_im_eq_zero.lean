-- Prove2me | Theorems.Thm_D1Bound5_quadInt_eq_intCast_of_im_eq_zero
-- name    : D1Bound5.quadInt_eq_intCast_of_im_eq_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:36:29.545644+00:00
-- url     : https://prove2.me/theorems/963cfa64-e45f-4580-93d1-4f5ad2f0f90b
-- title:
--   Quad Int eq int Cast of im eq zero
-- statement:
--   An element with zero imaginary coordinate is its ordinary integer real coordinate. No sign or discriminant hypothesis is needed.
-- source:
--   D1Bound5/PairNegativeIntegerObstruction.lean, lines 5-12, SHA-256 099be79d73801fcfb76bdc30024dc74b43ab6bdb2e935fcd75d8e115af902e02. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5


theorem _root_.D1Bound5.quadInt_eq_intCast_of_im_eq_zero {tau nu : ℤ}
    (z : QuadInt tau nu) (him : z.im = 0) :
    z = (z.re : QuadInt tau nu) := by sorry









end D1Bound5
end

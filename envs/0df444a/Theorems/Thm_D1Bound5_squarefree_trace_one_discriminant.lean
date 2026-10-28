-- Prove2me | Theorems.Thm_D1Bound5_squarefree_trace_one_discriminant
-- name    : D1Bound5.squarefree_trace_one_discriminant
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:28:49.574064+00:00
-- url     : https://prove2.me/theorems/930f0f4a-113e-4853-81f8-0561adfc14c8
-- title:
--   Squarefree trace one discriminant
-- statement:
--   A trace-one coordinate model for a full imaginary quadratic integer ring has squarefree absolute discriminant.
-- source:
--   D1Bound5/MaximalCoordinates.lean, lines 74-99, SHA-256 db32306018b4cc9c601d0bd15648a6675ec234d51750d3dd04f9988129483527. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
open scoped NumberField
open Module Polynomial

namespace D1Bound5

variable {K : Type*} [Field K]



variable [NumberField K]






theorem _root_.D1Bound5.squarefree_trace_one_discriminant {nu : ℤ}
    (e : QuadInt 1 nu ≃+* 𝓞 K) (hd : 0 < QuadInt.discriminant 1 nu) :
    Squarefree (QuadInt.discriminant 1 nu) := by sorry



end D1Bound5
end

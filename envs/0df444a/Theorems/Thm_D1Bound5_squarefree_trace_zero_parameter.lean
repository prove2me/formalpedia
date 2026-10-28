-- Prove2me | Theorems.Thm_D1Bound5_squarefree_trace_zero_parameter
-- name    : D1Bound5.squarefree_trace_zero_parameter
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:12:39.283203+00:00
-- url     : https://prove2.me/theorems/c7ccaa2b-0316-40c3-bcdb-b3ce8320d682
-- title:
--   Squarefree trace zero parameter
-- statement:
--   A trace-zero coordinate model for a full imaginary quadratic integer ring has squarefree nu.
-- source:
--   D1Bound5/MaximalCoordinates.lean, lines 57-72, SHA-256 db32306018b4cc9c601d0bd15648a6675ec234d51750d3dd04f9988129483527. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.squarefree_trace_zero_parameter {nu : ℤ}
    (e : QuadInt 0 nu ≃+* 𝓞 K) (hd : 0 < QuadInt.discriminant 0 nu) : Squarefree nu := by sorry





end D1Bound5
end

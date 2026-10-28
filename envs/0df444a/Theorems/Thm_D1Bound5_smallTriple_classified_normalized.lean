-- Prove2me | Theorems.Thm_D1Bound5_smallTriple_classified_normalized
-- name    : D1Bound5.smallTriple_classified_normalized
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:12:32.445785+00:00
-- url     : https://prove2.me/theorems/3efac433-9a9a-4a55-9c64-bc2fd65da9f9
-- title:
--   Small Triple classified normalized
-- statement:
--   Complete classification over every positive normalized coordinate model.
-- source:
--   D1Bound5/SmallTripleClassification.lean, lines 58-72, SHA-256 29c06a840b00bae4fa8a3417f349d7002808f0195fa16482f0c5528783af6485. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallTripleCheck_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt




theorem _root_.D1Bound5.smallTriple_classified_normalized {tau nu : ℤ}
    (htau : tau = 0 ∨ tau = 1) (hpos : 0 < discriminant tau nu)
    (t : Fin 3 → QuadInt tau nu) (ht : IsD1Tuple t)
    (hnorm : ∀ i, (t i).norm ≤ 8) :
    tripleCoordinates (t 0) (t 1) (t 2) ∈ smallTripleTable tau nu := by sorry



end D1Bound5
end

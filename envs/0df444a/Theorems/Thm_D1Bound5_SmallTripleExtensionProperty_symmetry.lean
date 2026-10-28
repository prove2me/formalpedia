-- Prove2me | Theorems.Thm_D1Bound5_SmallTripleExtensionProperty_symmetry
-- name    : D1Bound5.SmallTripleExtensionProperty.symmetry
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:15:51.217995+00:00
-- url     : https://prove2.me/theorems/fec8bdd4-cef7-4a5f-9466-b57f9ba1f361
-- title:
--   Small Triple Extension Property — symmetry
-- statement:
--   Proper extension uniqueness and the norm bound survive each of the four simultaneous sign/conjugation symmetries.
-- source:
--   D1Bound5/SmallExtensionSymmetry.lean, lines 93-122, SHA-256 67e063ccef711bfed6c0611c0e702166cb5f5a03a9533a5385fe57ef43b16f48. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt




















theorem _root_.D1Bound5.SmallTripleExtensionProperty.symmetry {tau nu : ℤ}
    (A : Finset (QuadInt tau nu)) (hA : SmallTripleExtensionProperty A)
    (sgn conj : Bool) :
    SmallTripleExtensionProperty (A.image (smallExtensionSymmetry sgn conj)) := by sorry







end D1Bound5
end

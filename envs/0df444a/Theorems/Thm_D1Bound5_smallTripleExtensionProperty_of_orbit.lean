-- Prove2me | Theorems.Thm_D1Bound5_smallTripleExtensionProperty_of_orbit
-- name    : D1Bound5.smallTripleExtensionProperty_of_orbit
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:42:02.632511+00:00
-- url     : https://prove2.me/theorems/1da9afa2-265a-41f5-bf60-37ddd055e6ba
-- title:
--   Small Triple Extension Property of orbit
-- statement:
--   The explicit coordinate orbit in the finite classification is exactly covered by the four proved norm-preserving extension symmetries.
-- source:
--   D1Bound5/SmallExtensionSymmetry.lean, lines 132-160, SHA-256 67e063ccef711bfed6c0611c0e702166cb5f5a03a9533a5385fe57ef43b16f48. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTripleData_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt


























theorem _root_.D1Bound5.smallTripleExtensionProperty_of_orbit {tau nu : ℤ}
    (row row' : Finset (ℤ × ℤ))
    (hrow : SmallTripleExtensionProperty (smallCoordinateSet tau nu row))
    (horbit : row' ∈ smallTripleOrbit tau row) :
    SmallTripleExtensionProperty (smallCoordinateSet tau nu row') := by sorry

end D1Bound5
end

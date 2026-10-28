-- Prove2me | Theorems.Thm_D1Bound5_smallPairGraphProperty_of_orbit
-- name    : D1Bound5.smallPairGraphProperty_of_orbit
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:29:53.712858+00:00
-- url     : https://prove2.me/theorems/fbe7bd6c-a0e2-4f3b-9379-d65389d904f0
-- title:
--   Small Pair Graph Property of orbit
-- statement:
--   Auxiliary result `smallPairGraphProperty_of_orbit` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphSymmetry.lean, lines 68-94, SHA-256 fe95f828c789959447eda784c0aa5f4516dacd522e3da889399545aa071a7bef. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt









theorem _root_.D1Bound5.smallPairGraphProperty_of_orbit {tau nu : ℤ}
    (row row' : Finset (ℤ × ℤ))
    (hrow : SmallPairGraphProperty (smallCoordinateSet tau nu row))
    (horbit : row' ∈ smallTripleOrbit tau row) :
    SmallPairGraphProperty (smallCoordinateSet tau nu row') := by sorry

end D1Bound5
end

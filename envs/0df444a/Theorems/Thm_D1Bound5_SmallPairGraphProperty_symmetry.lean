-- Prove2me | Theorems.Thm_D1Bound5_SmallPairGraphProperty_symmetry
-- name    : D1Bound5.SmallPairGraphProperty.symmetry
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:18:00.614851+00:00
-- url     : https://prove2.me/theorems/702adef5-6a64-4eac-acfd-d83e8c9d0578
-- title:
--   Small Pair Graph Property — symmetry
-- statement:
--   The entire triangle exclusion, including all three compatibility edges, transports through each simultaneous sign/conjugation symmetry.
-- source:
--   D1Bound5/SmallPairGraphSymmetry.lean, lines 31-62, SHA-256 fe95f828c789959447eda784c0aa5f4516dacd522e3da889399545aa071a7bef. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt






theorem _root_.D1Bound5.SmallPairGraphProperty.symmetry {tau nu : ℤ}
    (A : Finset (QuadInt tau nu)) (hA : SmallPairGraphProperty A)
    (sgn conj : Bool) :
    SmallPairGraphProperty (A.image (smallExtensionSymmetry sgn conj)) := by sorry





end D1Bound5
end

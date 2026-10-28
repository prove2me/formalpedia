-- Prove2me | Theorems.Thm_D1Bound5_smallTripleTable_1_1_extension_property_full_ring
-- name    : D1Bound5.smallTripleTable_1_1_extension_property_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:14:22.859259+00:00
-- url     : https://prove2.me/theorems/113aa818-7340-4f14-a4af-bcad8ba6222b
-- title:
--   Small Triple Table 1 1 extension property full ring
-- statement:
--   Auxiliary result `smallTripleTable_1_1_extension_property_full_ring` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleOrbitProperties.lean, lines 67-90, SHA-256 07ff15f6c03ab8e7ee1a1b77d6f2898bc846565283f65a83ca1bf04790a167ce. Project: https://github.com/tomislav-math/d1-bound5-lean

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







theorem _root_.D1Bound5.smallTripleTable_1_1_extension_property_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 1 ≃+* 𝓞 K)
    (row : Finset (ℤ × ℤ)) (hrow : row ∈ smallTripleTable 1 1) :
    SmallTripleExtensionProperty (smallCoordinateSet 1 1 row) := by sorry





end D1Bound5
end

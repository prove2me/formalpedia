-- Prove2me | Theorems.Thm_D1Bound5_smallTripleTable_extension_property_full_ring
-- name    : D1Bound5.smallTripleTable_extension_property_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:11.600903+00:00
-- url     : https://prove2.me/theorems/36830237-2d10-4aed-a358-b8126d9e1964
-- title:
--   Small Triple Table extension property full ring
-- statement:
--   All 24 coordinate triples inherit the representative extension theorem; no ordering or unproved symmetry convention is imposed on the input row.
-- source:
--   D1Bound5/SmallTripleOrbitProperties.lean, lines 113-127, SHA-256 07ff15f6c03ab8e7ee1a1b77d6f2898bc846565283f65a83ca1bf04790a167ce. Project: https://github.com/tomislav-math/d1-bound5-lean

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












theorem _root_.D1Bound5.smallTripleTable_extension_property_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K)
    (hmodel : (tau = 0 ∧ nu = 1) ∨ (tau = 0 ∧ nu = 2) ∨
      (tau = 1 ∧ nu = 1) ∨ (tau = 1 ∧ nu = 2))
    (row : Finset (ℤ × ℤ)) (hrow : row ∈ smallTripleTable tau nu) :
    SmallTripleExtensionProperty (smallCoordinateSet tau nu row) := by sorry

end D1Bound5
end

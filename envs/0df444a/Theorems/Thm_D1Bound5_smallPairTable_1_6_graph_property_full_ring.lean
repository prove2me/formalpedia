-- Prove2me | Theorems.Thm_D1Bound5_smallPairTable_1_6_graph_property_full_ring
-- name    : D1Bound5.smallPairTable_1_6_graph_property_full_ring
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:39:00.618022+00:00
-- url     : https://prove2.me/theorems/3a982a42-31f7-4009-b553-963d86de2ba0
-- title:
--   Small Pair Table 1 6 graph property full ring
-- statement:
--   Auxiliary result `smallPairTable_1_6_graph_property_full_ring` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairOrbitProperties.lean, lines 318-337, SHA-256 4aaf9e9c32b323b6121de5e879d561ffcd195b5099816cb6c0736c14b2987a2e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Ring.Abs
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
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
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
import Definitions.Def_D1Bound5_SmallPairClassificationData_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphSymmetry_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt





















theorem _root_.D1Bound5.smallPairTable_1_6_graph_property_full_ring
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 6 ≃+* 𝓞 K)
    (row : Finset (ℤ × ℤ)) (hrow : row ∈ smallPairTable 1 6) :
    SmallPairGraphProperty (smallCoordinateSet 1 6 row) := by sorry





end D1Bound5
end

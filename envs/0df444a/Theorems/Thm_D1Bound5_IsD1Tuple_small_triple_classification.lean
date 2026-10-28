-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_small_triple_classification
-- name    : D1Bound5.IsD1Tuple.small_triple_classification
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:06:27.514328+00:00
-- url     : https://prove2.me/theorems/16c6d70a-5a85-4f47-b5d9-9536604a4570
-- title:
--   Is D1Tuple — small triple classification
-- statement:
--   Full-ring small-triple classification: precisely four coordinate models are possible, and the unordered triple lies in the explicit 24-entry table. The models are the full rings for d = 1, 2, 3, 7 respectively.
-- source:
--   D1Bound5/SmallTripleClassification.lean, lines 74-118, SHA-256 29c06a840b00bae4fa8a3417f349d7002808f0195fa16482f0c5528783af6485. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.IsD1Tuple.small_triple_classification
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 3 → 𝓞 K) (ht : IsD1Tuple t)
    (hsmall : ∀ i, ‖phi (t i : K)‖ < 3) :
    ∃ (tau nu : ℤ) (e : QuadInt tau nu ≃+* 𝓞 K),
      ((tau = 0 ∧ nu = 1) ∨ (tau = 0 ∧ nu = 2) ∨
       (tau = 1 ∧ nu = 1) ∨ (tau = 1 ∧ nu = 2)) ∧
      tripleCoordinates (e.symm (t 0)) (e.symm (t 1)) (e.symm (t 2)) ∈
        smallTripleTable tau nu := by sorry

end D1Bound5
end

-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_small_pair_classification
-- name    : D1Bound5.IsD1Tuple.small_pair_classification
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:17:01.024569+00:00
-- url     : https://prove2.me/theorems/40f54ae4-caba-4c1e-b7c3-acee70df6f53
-- title:
--   Is D1Tuple — small pair classification
-- statement:
--   Every nondegenerate compatible pair of small actual algebraic integers belongs to one of the48explicit sign/conjugation orbits. The finite tables are complete and maximality has removed all extra coordinate orders.
-- source:
--   D1Bound5/SmallPairClassification.lean, lines 52-96, SHA-256 a32a3e7b2d5dfed4754fd2fe6af26c9e86156fe171110d66d6c2f3d17661c981. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairClassificationCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairClassificationData_Definitions
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt






theorem _root_.D1Bound5.IsD1Tuple.small_pair_classification
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 2 → 𝓞 K) (ht : IsD1Tuple t)
    (hsmall : ∀ i, ‖phi (t i : K)‖ < 3)
    (hnondeg : t 0*t 1+1 ≠ 0) :
    ∃ (tau nu : ℤ) (e : QuadInt tau nu ≃+* 𝓞 K),
      (tau,nu) ∈ smallPairModels ∧
      pairCoordinates (e.symm (t 0)) (e.symm (t 1)) ∈ smallPairTable tau nu := by sorry

end D1Bound5
end

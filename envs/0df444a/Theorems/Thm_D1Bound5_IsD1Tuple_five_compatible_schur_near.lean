-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_five_compatible_schur_near
-- name    : D1Bound5.IsD1Tuple.five_compatible_schur_near
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:08:15.407782+00:00
-- url     : https://prove2.me/theorems/34183743-6b88-4b78-b3e6-703bbba4db64
-- title:
--   Is D1Tuple — five compatible schur near
-- statement:
--   The Schur complement of a single compatible integral signed root matrix for an actual ordered D(1) quintuple lies within 1/2 of the reference matrix. No independent Schur or sign assumptions are made.
-- source:
--   D1Bound5/ProductFiveTupleSchur.lean, lines 9-80, SHA-256 d4a0f1109303fe35cbf779bf9bf6e99bcb95b1e2dc653fd7ccae86a84127beaf. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_ProductFiveArithmeticClosure_Definitions
import Definitions.Def_D1Bound5_ProductFiveCompatibleSigns_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions

section
open scoped NumberField Matrix.Norms.L2Operator
open Matrix Module

namespace D1Bound5


theorem _root_.D1Bound5.IsD1Tuple.five_compatible_schur_near
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hB : 3 ≤ ‖phi (a 1 : K)‖)
    (u : Fin 5 → ℂ) (S : Matrix (Fin 5) (Fin 5) (𝓞 K))
    (hu : ∀ i, (u i)^2 = phi (a i : K))
    (hdiag : ∀ i, S i i = a i)
    (hgood : ∀ i j, i ≠ j →
      FiveSignedEntryGood (phi.comp (algebraMap (𝓞 K) K)) a u i j (S i j)) :
    ‖fiveNormalizedSchur (fun i => phi (a i : K)) u
      (S.map (phi.comp (algebraMap (𝓞 K) K))) -
      halfOffDiagonal‖ < (1/2 : ℝ) := by sorry



end D1Bound5
end

-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_five_compatible_schur_det_small
-- name    : D1Bound5.IsD1Tuple.five_compatible_schur_det_small
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:06:47.687066+00:00
-- url     : https://prove2.me/theorems/fa45a968-f4fa-468e-9a45-41975be84c52
-- title:
--   Is D1Tuple — five compatible schur det small
-- statement:
--   One compatible signed integral root matrix attached to an actual ordered D(1) quintuple satisfies the sharp Schur determinant estimate. The size, sign, inverse and bilinear hypotheses are derived from the tuple itself.
-- source:
--   D1Bound5/ProductFiveTupleGrowth.lean, lines 9-95, SHA-256 80d98052c4994147171c28574e3e10fcf54fe865d2b39c5d757ddcc0ffb46c5d. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open scoped NumberField Matrix.Norms.L2Operator
open Matrix Module

namespace D1Bound5


theorem _root_.D1Bound5.IsD1Tuple.five_compatible_schur_det_small
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hB : 3 ≤ ‖phi (a 1 : K)‖)
    (u : Fin 5 → ℂ) (S : Matrix (Fin 5) (Fin 5) (𝓞 K))
    (hu : ∀ i, (u i)^2 = phi (a i : K))
    (hdiag : ∀ i, S i i = a i)
    (hSsym : ∀ i j, S i j = S j i)
    (hgood : ∀ i j, i ≠ j →
      FiveSignedEntryGood (phi.comp (algebraMap (𝓞 K) K)) a u i j (S i j)) :
    ‖(fiveNormalizedSchur (fun i => phi (a i : K)) u
      (S.map (phi.comp (algebraMap (𝓞 K) K)))).det‖ < (1/3 : ℝ) := by sorry



end D1Bound5
end

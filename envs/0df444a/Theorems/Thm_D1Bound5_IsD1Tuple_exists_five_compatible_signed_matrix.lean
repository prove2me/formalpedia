-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_exists_five_compatible_signed_matrix
-- name    : D1Bound5.IsD1Tuple.exists_five_compatible_signed_matrix
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:06:49.997609+00:00
-- url     : https://prove2.me/theorems/ec1bd0f9-6e09-4a97-98cf-7421fb56ae59
-- title:
--   Is D1Tuple — exists five compatible signed matrix
-- statement:
--   The actual ordered full-integer-ring D(1) quintuple supplies every threshold: no unproved sign-existence or large-last-entry hypothesis remains.
-- source:
--   D1Bound5/ProductFiveCompatibleSigns.lean, lines 297-353, SHA-256 7ef326eadce635a2fc8001d19ab9a7846a67febccdcf6d3cfe50963ad72c4cef. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
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
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_ProductFiveCompatibleSigns_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions

section
namespace D1Bound5

















open scoped NumberField
open Module




theorem _root_.D1Bound5.IsD1Tuple.exists_five_compatible_signed_matrix
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hA : 1 ≤ ‖phi (a 0 : K)‖) (hB : 3 ≤ ‖phi (a 1 : K)‖) :
    let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
    ∃ (u : Fin 5 → ℂ) (S : Matrix (Fin 5) (Fin 5) (𝓞 K)),
      (∀ i, (u i)^2 = f (a i)) ∧
      (∀ i, S i i = a i) ∧
      (∀ i j, S i j = S j i) ∧
      (∀ i j, i ≠ j → (S i j)^2 = a i*a j+1) ∧
      (∀ i j, i ≠ j → FiveSignedEntryGood f a u i j (S i j)) ∧
      ‖(fivePrefixError (normalizedRootError (fun i => f (a i)) u
        (fun i j => f (S i j)))).det‖ < (33/128 : ℝ) ∧
      (∀ i : Fin 4,
        ‖fiveLastError (normalizedRootError (fun k => f (a k)) u
          (fun k l => f (S k l))) i - (1/2 : ℂ)‖ < (1/400 : ℝ)) := by sorry




end D1Bound5
end

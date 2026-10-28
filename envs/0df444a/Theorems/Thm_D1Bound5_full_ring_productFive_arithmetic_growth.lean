-- Prove2me | Theorems.Thm_D1Bound5_full_ring_productFive_arithmetic_growth
-- name    : D1Bound5.full_ring_productFive_arithmetic_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:17:43.695997+00:00
-- url     : https://prove2.me/theorems/775b7215-0e18-48f5-b678-92b8b74c7330
-- title:
--   Full ring product Five arithmetic growth
-- statement:
--   Arithmetic final step of product-five in the full ring of integers of every imaginary quadratic field. Only the two explicit analytic Schur estimates remain as hypotheses; nonsingularity of the integral determinant is derived, not assumed.
-- source:
--   D1Bound5/ProductFiveArithmeticClosure.lean, lines 54-139, SHA-256 0da19bb1f7a607bd1cb647f269c6c5f92cae2602755ad9eddbe0deb76e5a496d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ProductFiveArithmeticClosure_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions

section
open scoped NumberField BigOperators Matrix.Norms.L2Operator
open Matrix Module

namespace D1Bound5








theorem _root_.D1Bound5.full_ring_productFive_arithmetic_growth
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (M : Matrix (Fin 5) (Fin 5) (𝓞 K))
    (u : Fin 5 → ℂ)
    (hu : ∀ i, (u i)^2 = phi (a i : K))
    (hdiag : ∀ i, M i i = a i)
    (hsym : ∀ i j, M i j = M j i)
    (hd : fiveLastValue (fun i => phi (a i : K)) ≠ 0)
    (hGne : (fiveNormalizedSchur
        (fun i => phi (a i : K)) u
        (M.map (phi.comp (algebraMap (𝓞 K) K)))).det ≠ 0)
    (hGlt : ‖(fiveNormalizedSchur
        (fun i => phi (a i : K)) u
        (M.map (phi.comp (algebraMap (𝓞 K) K)))).det‖ < (1/3 : ℝ)) :
    3 * (∏ i : Fin 4, ‖phi (a (Fin.castAdd 1 i) : K)‖) <
      ‖phi (a 4 : K)‖ := by sorry



end D1Bound5
end

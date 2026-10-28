-- Prove2me | Theorems.Thm_D1Bound5_five_root_det_ne_zero_of_schur
-- name    : D1Bound5.five_root_det_ne_zero_of_schur
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:08:48.54542+00:00
-- url     : https://prove2.me/theorems/069e1193-707a-40d5-8d07-432db5558d76
-- title:
--   Five root det ne zero of schur
-- statement:
--   Nonvanishing of the Schur determinant forces the original symmetric five-entry root matrix to have nonzero determinant. No assumption on any individual root or on the leading four-by-four determinant is needed.
-- source:
--   D1Bound5/ProductFiveArithmeticClosure.lean, lines 19-36, SHA-256 0da19bb1f7a607bd1cb647f269c6c5f92cae2602755ad9eddbe0deb76e5a496d. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.five_root_det_ne_zero_of_schur
    (t u : Fin 5 → ℂ) (M : Matrix (Fin 5) (Fin 5) ℂ)
    (hu : ∀ i, (u i)^2 = t i)
    (hdiag : ∀ i, M i i = t i)
    (hsym : Mᵀ = M)
    (hd : fiveLastValue t ≠ 0)
    (hG : (fiveNormalizedSchur t u M).det ≠ 0) :
    M.det ≠ 0 := by sorry







end D1Bound5
end

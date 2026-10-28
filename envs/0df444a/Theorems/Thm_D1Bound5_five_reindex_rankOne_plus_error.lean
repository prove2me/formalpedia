-- Prove2me | Theorems.Thm_D1Bound5_five_reindex_rankOne_plus_error
-- name    : D1Bound5.five_reindex_rankOne_plus_error
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:46:35.326737+00:00
-- url     : https://prove2.me/theorems/1f5270e2-190f-4694-8e11-bf7f6f3fb904
-- title:
--   Five reindex rank One plus error
-- statement:
--   The exact five-by-five block structure of a symmetric normalized root matrix. No invertibility or nonzero tuple hypotheses are needed.
-- source:
--   D1Bound5/ProductFiveMatrixBridge.lean, lines 25-72, SHA-256 8ea3704fb4c1308113f0fd79cdba0ca29b02390fb0ce0be51946ee093a9ecedc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ProductFiveBlockDet_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions

section
open Matrix

namespace D1Bound5










theorem _root_.D1Bound5.five_reindex_rankOne_plus_error
    (t : Fin 5 → ℂ) (E : Matrix (Fin 5) (Fin 5) ℂ)
    (hdiag : E (Fin.natAdd 4 (0 : Fin 1)) (Fin.natAdd 4 (0 : Fin 1)) = 0)
    (hsym : Eᵀ = E) :
    Matrix.reindex (finSumFinEquiv : Fin 4 ⊕ Fin 1 ≃ Fin 5).symm
      (finSumFinEquiv : Fin 4 ⊕ Fin 1 ≃ Fin 5).symm
      (fun i j => t i * t j + E i j) =
      productFiveIntegratedBlock
        (fivePrefixError E) (fiveLastError E)
        (fivePrefixValues t) (fiveLastValue t) := by sorry





end D1Bound5
end

-- Prove2me | Theorems.Thm_D1Bound5_scalar_last_block_det
-- name    : D1Bound5.scalar_last_block_det
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:03.432568+00:00
-- url     : https://prove2.me/theorems/5b9227ef-a723-4c70-af93-5bc4b41311b0
-- title:
--   Scalar last block det
-- statement:
--   Scalar Schur determinant identity without invertibility of the leading block.
-- source:
--   D1Bound5/ProductFiveBlockDet.lean, lines 8-47, SHA-256 10e7a7c95556fd99f1056a1878c1c35778ba742ada21bee32a4eb5948f7ada68. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open Matrix

namespace D1Bound5


theorem _root_.D1Bound5.scalar_last_block_det
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (b c : n → ℂ) (d : ℂ) (hd : d ≠ 0) :
    (Matrix.fromBlocks A (fun i (_ : Fin 1) => b i)
      (fun (_ : Fin 1) j => c j)
      (fun (_ _ : Fin 1) => d)).det =
      d * (A - Matrix.of (fun i j => b i * c j / d)).det := by sorry





end D1Bound5
end

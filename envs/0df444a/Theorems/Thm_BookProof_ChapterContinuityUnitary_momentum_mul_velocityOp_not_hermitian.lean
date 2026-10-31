-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitary_momentum_mul_velocityOp_not_hermitian
-- name    : BookProof.ChapterContinuityUnitary.momentum_mul_velocityOp_not_hermitian
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T12:01:48.868117+00:00
-- url     : https://prove2.me/theorems/43bbefdc-65ec-4660-9cf6-c140240513dd
-- title:
--   The Lean 4 theorem `momentum_mul_velocityOp_not_hermitian` in the `ChapterContinuityUnitary` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `momentum_mul_velocityOp_not_hermitian` in the `ChapterContinuityUnitary` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterContinuityUnitary.lean

-- Generated from ChapterContinuityUnitary.lean — theorem BookProof.ChapterContinuityUnitary.momentum_mul_velocityOp_not_hermitian
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]


open scoped BigOperators Matrix TensorProduct

theorem BookProof.ChapterContinuityUnitary.momentum_mul_velocityOp_not_hermitian :
    (momentum 3 * velocityOp (fun k => (k.val : ℝ)))ᴴ
      ≠ momentum 3 * velocityOp (fun k => (k.val : ℝ)) := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterE3_eulerJ_sq
-- name    : BookProof.ChapterE3.eulerJ_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:12:50.99726+00:00
-- url     : https://prove2.me/theorems/f8a8f602-956e-4cb6-8d20-e9be2da12a27
-- title:
--   `BookProof.ChapterE3.eulerJ_sq` (l w : Fin n → ℝ) (hll : ∑ i, l i * l i = 1) (hww : ∑ i, w i * w i = 1) (hlw : ∑ i, l i * w i = 0) : eulerJ l w * eulerJ l w = - (Matrix.vecMulVec l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE3`.
--
--   `BookProof.ChapterE3.eulerJ_sq` (l w : Fin n → ℝ) (hll : ∑ i, l i * l i = 1) (hww : ∑ i, w i * w i = 1) (hlw : ∑ i, l i * w i = 0) : eulerJ l w * eulerJ l w = - (Matrix.vecMulVec l l + Matrix.vecMulVec w w)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE3.eulerJ_sq`.

-- Generated from ChapterE3.lean — theorem BookProof.ChapterE3.eulerJ_sq
import Mathlib
import Definitions.Def_ChapterE3
open BookProof.ChapterE3


open scoped Matrix BigOperators


variable {n : ℕ}

theorem BookProof.ChapterE3.eulerJ_sq (l w : Fin n → ℝ)
    (hll : ∑ i, l i * l i = 1) (hww : ∑ i, w i * w i = 1)
    (hlw : ∑ i, l i * w i = 0) :
    eulerJ l w * eulerJ l w = - (Matrix.vecMulVec l l + Matrix.vecMulVec w w) := by sorry

-- Prove2me | Theorems.Thm_BookProof_AbelianDiagonal_diagonal_commute
-- name    : BookProof.AbelianDiagonal.diagonal_commute
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:50:09.611982+00:00
-- url     : https://prove2.me/theorems/83f5f81c-3347-4537-b387-def4cb5b31c8
-- title:
--   `BookProof.AbelianDiagonal.diagonal_commute` (d e : n → ℂ) : Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianDiagonal`.
--
--   `BookProof.AbelianDiagonal.diagonal_commute` (d e : n → ℂ) : Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d
--
--   Formalization note: Lean 4 identifier `BookProof.AbelianDiagonal.diagonal_commute`.

-- Generated from ChapterAbelianDiagonal.lean — theorem BookProof.AbelianDiagonal.diagonal_commute
import Mathlib
import Definitions.Def_ChapterAbelianDiagonal
open BookProof.AbelianDiagonal



open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.AbelianDiagonal.diagonal_commute (d e : n → ℂ) :
    Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d := by sorry

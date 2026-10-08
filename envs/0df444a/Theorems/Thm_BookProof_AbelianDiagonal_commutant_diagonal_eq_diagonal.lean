-- Prove2me | Theorems.Thm_BookProof_AbelianDiagonal_commutant_diagonal_eq_diagonal
-- name    : BookProof.AbelianDiagonal.commutant_diagonal_eq_diagonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:50:16.55706+00:00
-- url     : https://prove2.me/theorems/54dc64c1-ee30-4487-a9d9-afd6aa411dc4
-- title:
--   `BookProof.AbelianDiagonal.commutant_diagonal_eq_diagonal` (M : Matrix n n ℂ) (h : ∀ d : n → ℂ, M * Matrix.diagonal d = Matrix.diagonal d * M) : M = Matrix.diagonal (fun i => M i i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianDiagonal`.
--
--   `BookProof.AbelianDiagonal.commutant_diagonal_eq_diagonal` (M : Matrix n n ℂ) (h : ∀ d : n → ℂ, M * Matrix.diagonal d = Matrix.diagonal d * M) : M = Matrix.diagonal (fun i => M i i)
--
--   Formalization note: Lean 4 identifier `BookProof.AbelianDiagonal.commutant_diagonal_eq_diagonal`.

-- Generated from ChapterAbelianDiagonal.lean — theorem BookProof.AbelianDiagonal.commutant_diagonal_eq_diagonal
import Mathlib
import Definitions.Def_ChapterAbelianDiagonal
open BookProof.AbelianDiagonal



open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.AbelianDiagonal.commutant_diagonal_eq_diagonal (M : Matrix n n ℂ)
    (h : ∀ d : n → ℂ, M * Matrix.diagonal d = Matrix.diagonal d * M) :
    M = Matrix.diagonal (fun i => M i i) := by sorry

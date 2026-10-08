-- Prove2me | Theorems.Thm_BookProof_AbelianDiagonal_vonNeumann_abelian_typeI_case
-- name    : BookProof.AbelianDiagonal.vonNeumann_abelian_typeI_case
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:50:33.99458+00:00
-- url     : https://prove2.me/theorems/a7820980-f302-4303-b7e6-df0fccbcad34
-- title:
--   `BookProof.AbelianDiagonal.vonNeumann_abelian_typeI_case` : Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ) ∧ (∀ d e : n → ℂ, Matrix.diagonal d *...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianDiagonal`.
--
--   `BookProof.AbelianDiagonal.vonNeumann_abelian_typeI_case` : Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ) ∧ (∀ d e : n → ℂ, Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d) ∧ (∀ M : Matrix n n ℂ, (∀ d : n → ℂ, M * Matrix.diagonal d = Matrix.diagonal d * M) ↔ ∃ e : n → ℂ, M = Matrix.diagonal e)
--
--   Formalization note: Lean 4 identifier `BookProof.AbelianDiagonal.vonNeumann_abelian_typeI_case`.

-- Generated from ChapterAbelianDiagonal.lean — theorem BookProof.AbelianDiagonal.vonNeumann_abelian_typeI_case
import Mathlib
import Definitions.Def_ChapterAbelianDiagonal
open BookProof.AbelianDiagonal



open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.AbelianDiagonal.vonNeumann_abelian_typeI_case :
    Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ) ∧
      (∀ d e : n → ℂ,
        Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d) ∧
      (∀ M : Matrix n n ℂ,
        (∀ d : n → ℂ, M * Matrix.diagonal d = Matrix.diagonal d * M) ↔
          ∃ e : n → ℂ, M = Matrix.diagonal e) := by sorry

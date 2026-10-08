-- Prove2me | Theorems.Thm_BookProof_AbelianDiagonal_diagonalStarAlgHom_injective
-- name    : BookProof.AbelianDiagonal.diagonalStarAlgHom_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:50:26.631979+00:00
-- url     : https://prove2.me/theorems/a8565d44-1109-4a62-be10-66aebb1100b8
-- title:
--   `BookProof.AbelianDiagonal.diagonalStarAlgHom_injective` : Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianDiagonal`.
--
--   `BookProof.AbelianDiagonal.diagonalStarAlgHom_injective` : Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.AbelianDiagonal.diagonalStarAlgHom_injective`.

-- Generated from ChapterAbelianDiagonal.lean — theorem BookProof.AbelianDiagonal.diagonalStarAlgHom_injective
import Mathlib
import Definitions.Def_ChapterAbelianDiagonal
open BookProof.AbelianDiagonal



open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.AbelianDiagonal.diagonalStarAlgHom_injective :
    Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ) := by sorry

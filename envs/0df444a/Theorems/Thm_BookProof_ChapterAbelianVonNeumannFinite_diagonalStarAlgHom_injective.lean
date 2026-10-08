-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianVonNeumannFinite_diagonalStarAlgHom_injective
-- name    : BookProof.ChapterAbelianVonNeumannFinite.diagonalStarAlgHom_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:51:52.451196+00:00
-- url     : https://prove2.me/theorems/8eb32b36-28ab-4b50-ab64-7c87f05c8b9f
-- title:
--   `BookProof.ChapterAbelianVonNeumannFinite.diagonalStarAlgHom_injective` : Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianVonNeumannFinite`.
--
--   `BookProof.ChapterAbelianVonNeumannFinite.diagonalStarAlgHom_injective` : Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianVonNeumannFinite.diagonalStarAlgHom_injective`.

-- Generated from ChapterAbelianVonNeumannFinite.lean — theorem BookProof.ChapterAbelianVonNeumannFinite.diagonalStarAlgHom_injective
import Mathlib
import Definitions.Def_ChapterAbelianVonNeumannFinite
import Definitions.Def_ChapterAbelianDiagonal
open BookProof.AbelianDiagonal
open BookProof.ChapterAbelianVonNeumannFinite


open Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ChapterAbelianVonNeumannFinite.diagonalStarAlgHom_injective :
    Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ) := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignMatrix_flipMatrix_xor
-- name    : BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_xor
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T08:00:26.293008+00:00
-- url     : https://prove2.me/theorems/542cc1d7-5f91-4b60-90c2-1929365cb2d1
-- title:
--   `BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_xor` (b₁ b₂ : Fin n → Bool) : flipMatrix (fun k => xor (b₁ k) (b₂ k)) = flipMatrix b₁ * flipMatrix b₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignMatrix`.
--
--   `BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_xor` (b₁ b₂ : Fin n → Bool) : flipMatrix (fun k => xor (b₁ k) (b₂ k)) = flipMatrix b₁ * flipMatrix b₂
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_xor`.

-- Generated from ChapterFreeFieldBornSignMatrix.lean — theorem BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_xor
import Definitions.Def_ChapterFreeFieldBornSignAction
import Definitions.Def_ChapterFreeFieldBornSignHom
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignMatrix

variable {n : ℕ}


open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom

theorem BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_xor (b₁ b₂ : Fin n → Bool) :
    flipMatrix (fun k => xor (b₁ k) (b₂ k)) = flipMatrix b₁ * flipMatrix b₂ := by sorry

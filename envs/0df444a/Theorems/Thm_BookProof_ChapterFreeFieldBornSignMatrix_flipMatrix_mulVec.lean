-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignMatrix_flipMatrix_mulVec
-- name    : BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_mulVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T07:58:48.91727+00:00
-- url     : https://prove2.me/theorems/20be68b6-75e3-42c3-9981-b67b9757e903
-- title:
--   `BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_mulVec` (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) : (flipMatrix b).mulVec x = boolFlip b x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignMatrix`.
--
--   `BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_mulVec` (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) : (flipMatrix b).mulVec x = boolFlip b x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_mulVec`.

-- Generated from ChapterFreeFieldBornSignMatrix.lean — theorem BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_mulVec
import Definitions.Def_ChapterFreeFieldBornSignAction
import Definitions.Def_ChapterFreeFieldBornSignHom
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignMatrix

variable {n : ℕ}


open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom

theorem BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_mulVec (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) :
    (flipMatrix b).mulVec x = boolFlip b x := by sorry

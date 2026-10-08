-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignMatrix_flipMatrix_sq
-- name    : BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T08:03:12.647631+00:00
-- url     : https://prove2.me/theorems/a608bbda-8344-4bcc-9bb5-25f21ab343a7
-- title:
--   `BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_sq` (b : Fin n → Bool) : flipMatrix b * flipMatrix b = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignMatrix`.
--
--   `BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_sq` (b : Fin n → Bool) : flipMatrix b * flipMatrix b = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_sq`.

-- Generated from ChapterFreeFieldBornSignMatrix.lean — theorem BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_sq
import Definitions.Def_ChapterFreeFieldBornSignAction
import Definitions.Def_ChapterFreeFieldBornSignHom
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignMatrix

variable {n : ℕ}


open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom

theorem BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_sq (b : Fin n → Bool) :
    flipMatrix b * flipMatrix b = 1 := by sorry

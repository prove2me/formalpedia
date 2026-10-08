-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientation_det_flipMatrix_eq_neg_one_iff
-- name    : BookProof.ChapterFreeFieldBornSignOrientation.det_flipMatrix_eq_neg_one_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T08:21:45.308242+00:00
-- url     : https://prove2.me/theorems/42373bb9-314b-413d-a7df-f7d46f5aa048
-- title:
--   `BookProof.ChapterFreeFieldBornSignOrientation.det_flipMatrix_eq_neg_one_iff` (b : Fin n → Bool) : Matrix.det (flipMatrix b) = -1 ↔ Odd (flipCount b)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignOrientation`.
--
--   `BookProof.ChapterFreeFieldBornSignOrientation.det_flipMatrix_eq_neg_one_iff` (b : Fin n → Bool) : Matrix.det (flipMatrix b) = -1 ↔ Odd (flipCount b)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignOrientation.det_flipMatrix_eq_neg_one_iff`.

-- Generated from ChapterFreeFieldBornSignOrientation.lean — theorem BookProof.ChapterFreeFieldBornSignOrientation.det_flipMatrix_eq_neg_one_iff
import Definitions.Def_ChapterFreeFieldBornSignAction
import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientation
open BookProof.ChapterFreeFieldBornSignOrientation

variable {n : ℕ}


open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix

theorem BookProof.ChapterFreeFieldBornSignOrientation.det_flipMatrix_eq_neg_one_iff (b : Fin n → Bool) :
    Matrix.det (flipMatrix b) = -1 ↔ Odd (flipCount b) := by sorry

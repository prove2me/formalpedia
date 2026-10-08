-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignMatrix_det_flipMatrix
-- name    : BookProof.ChapterFreeFieldBornSignMatrix.det_flipMatrix
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T08:04:12.877773+00:00
-- url     : https://prove2.me/theorems/5b649119-a834-4a42-817b-eb75d5be42fb
-- title:
--   `BookProof.ChapterFreeFieldBornSignMatrix.det_flipMatrix` (b : Fin n → Bool) : Matrix.det (flipMatrix b) = (-1 : ℝ) ^ flipCount b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignMatrix`.
--
--   `BookProof.ChapterFreeFieldBornSignMatrix.det_flipMatrix` (b : Fin n → Bool) : Matrix.det (flipMatrix b) = (-1 : ℝ) ^ flipCount b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignMatrix.det_flipMatrix`.

-- Generated from ChapterFreeFieldBornSignMatrix.lean — theorem BookProof.ChapterFreeFieldBornSignMatrix.det_flipMatrix
import Definitions.Def_ChapterFreeFieldBornSignAction
import Definitions.Def_ChapterFreeFieldBornSignHom
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignMatrix

variable {n : ℕ}


open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom

theorem BookProof.ChapterFreeFieldBornSignMatrix.det_flipMatrix (b : Fin n → Bool) :
    Matrix.det (flipMatrix b) = (-1 : ℝ) ^ flipCount b := by sorry

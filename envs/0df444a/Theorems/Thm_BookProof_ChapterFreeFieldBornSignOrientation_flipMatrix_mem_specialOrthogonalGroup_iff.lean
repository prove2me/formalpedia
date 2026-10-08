-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientation_flipMatrix_mem_specialOrthogonalGroup_iff
-- name    : BookProof.ChapterFreeFieldBornSignOrientation.flipMatrix_mem_specialOrthogonalGroup_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T08:25:37.259696+00:00
-- url     : https://prove2.me/theorems/a28751d8-a2bf-41e3-9b4a-c95ea9e436e1
-- title:
--   `BookProof.ChapterFreeFieldBornSignOrientation.flipMatrix_mem_specialOrthogonalGroup_iff` (b : Fin n → Bool) : flipMatrix b ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ ↔ Even (flipCo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignOrientation`.
--
--   `BookProof.ChapterFreeFieldBornSignOrientation.flipMatrix_mem_specialOrthogonalGroup_iff` (b : Fin n → Bool) : flipMatrix b ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ ↔ Even (flipCount b)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignOrientation.flipMatrix_mem_specialOrthogonalGroup_iff`.

-- Generated from ChapterFreeFieldBornSignOrientation.lean — theorem BookProof.ChapterFreeFieldBornSignOrientation.flipMatrix_mem_specialOrthogonalGroup_iff
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

theorem BookProof.ChapterFreeFieldBornSignOrientation.flipMatrix_mem_specialOrthogonalGroup_iff (b : Fin n → Bool) :
    flipMatrix b ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ ↔ Even (flipCount b) := by sorry

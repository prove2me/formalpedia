-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignRepresentation_flipMatrix_injective
-- name    : BookProof.ChapterFreeFieldBornSignRepresentation.flipMatrix_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:32:18.854183+00:00
-- url     : https://prove2.me/theorems/451fe341-6a04-4638-a309-74c42a12f07d
-- title:
--   `BookProof.ChapterFreeFieldBornSignRepresentation.flipMatrix_injective` : Function.Injective (flipMatrix : (Fin n → Bool) → Matrix (Fin n) (Fin n) ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignRepresentation`.
--
--   `BookProof.ChapterFreeFieldBornSignRepresentation.flipMatrix_injective` : Function.Injective (flipMatrix : (Fin n → Bool) → Matrix (Fin n) (Fin n) ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignRepresentation.flipMatrix_injective`.

-- Generated from ChapterFreeFieldBornSignRepresentation.lean — theorem BookProof.ChapterFreeFieldBornSignRepresentation.flipMatrix_injective
import Definitions.Def_ChapterFreeFieldBornSignAction
import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Definitions.Def_ChapterFreeFieldBornSignOrientation
import Definitions.Def_ChapterFreeFieldBornSignOrientationSubgroup
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignRepresentation
open BookProof.ChapterFreeFieldBornSignRepresentation


open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignOrientation
open BookProof.ChapterFreeFieldBornSignOrientationSubgroup


variable {n : ℕ}

theorem BookProof.ChapterFreeFieldBornSignRepresentation.flipMatrix_injective : Function.Injective (flipMatrix :
    (Fin n → Bool) → Matrix (Fin n) (Fin n) ℝ) := by sorry

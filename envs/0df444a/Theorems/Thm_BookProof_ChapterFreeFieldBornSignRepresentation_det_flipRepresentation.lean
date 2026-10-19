-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignRepresentation_det_flipRepresentation
-- name    : BookProof.ChapterFreeFieldBornSignRepresentation.det_flipRepresentation
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:32:52.123544+00:00
-- url     : https://prove2.me/theorems/6488caa1-72c0-4ab2-af5f-4572d8a18b84
-- title:
--   `BookProof.ChapterFreeFieldBornSignRepresentation.det_flipRepresentation` (b : Multiplicative (Fin n → Bool)) : Matrix.det (flipRepresentation n b : Matrix (Fin n) (Fin n) ℝ) = (-1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignRepresentation`.
--
--   `BookProof.ChapterFreeFieldBornSignRepresentation.det_flipRepresentation` (b : Multiplicative (Fin n → Bool)) : Matrix.det (flipRepresentation n b : Matrix (Fin n) (Fin n) ℝ) = (-1 : ℝ) ^ flipCount b.toAdd
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignRepresentation.det_flipRepresentation`.

-- Generated from ChapterFreeFieldBornSignRepresentation.lean — theorem BookProof.ChapterFreeFieldBornSignRepresentation.det_flipRepresentation
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

theorem BookProof.ChapterFreeFieldBornSignRepresentation.det_flipRepresentation (b : Multiplicative (Fin n → Bool)) :
    Matrix.det (flipRepresentation n b : Matrix (Fin n) (Fin n) ℝ) =
      (-1 : ℝ) ^ flipCount b.toAdd := by sorry

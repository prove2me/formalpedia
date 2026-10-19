-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignRepresentation_flipRepresentation_specialOrthogonal_iff
-- name    : BookProof.ChapterFreeFieldBornSignRepresentation.flipRepresentation_specialOrthogonal_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:32:23.770859+00:00
-- url     : https://prove2.me/theorems/5ee00752-c88e-4e22-a2f0-daae321a1032
-- title:
--   `BookProof.ChapterFreeFieldBornSignRepresentation.flipRepresentation_specialOrthogonal_iff` (b : Multiplicative (Fin n → Bool)) : (flipRepresentation n b : Matrix (Fin n) (Fin n) ℝ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignRepresentation`.
--
--   `BookProof.ChapterFreeFieldBornSignRepresentation.flipRepresentation_specialOrthogonal_iff` (b : Multiplicative (Fin n → Bool)) : (flipRepresentation n b : Matrix (Fin n) (Fin n) ℝ) ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ ↔ b.toAdd ∈ orientationPreservingSigns n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignRepresentation.flipRepresentation_specialOrthogonal_iff`.

-- Generated from ChapterFreeFieldBornSignRepresentation.lean — theorem BookProof.ChapterFreeFieldBornSignRepresentation.flipRepresentation_specialOrthogonal_iff
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

theorem BookProof.ChapterFreeFieldBornSignRepresentation.flipRepresentation_specialOrthogonal_iff
    (b : Multiplicative (Fin n → Bool)) :
    (flipRepresentation n b : Matrix (Fin n) (Fin n) ℝ) ∈
        Matrix.specialOrthogonalGroup (Fin n) ℝ ↔
      b.toAdd ∈ orientationPreservingSigns n := by sorry

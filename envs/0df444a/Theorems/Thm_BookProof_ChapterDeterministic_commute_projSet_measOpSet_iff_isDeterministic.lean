-- Prove2me | Theorems.Thm_BookProof_ChapterDeterministic_commute_projSet_measOpSet_iff_isDeterministic
-- name    : BookProof.ChapterDeterministic.commute_projSet_measOpSet_iff_isDeterministic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:22:05.970635+00:00
-- url     : https://prove2.me/theorems/42d3ae42-1a19-4d0a-b4d6-a0039d4e24d2
-- title:
--   `BookProof.ChapterDeterministic.commute_projSet_measOpSet_iff_isDeterministic` (U : Matrix (Fin n) (Fin n) ℂ) : (∀ A B : Finset (Fin n), Commute (projSet A) (measOpSet U B)) ↔ IsDe
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeterministic`.
--
--   `BookProof.ChapterDeterministic.commute_projSet_measOpSet_iff_isDeterministic` (U : Matrix (Fin n) (Fin n) ℂ) : (∀ A B : Finset (Fin n), Commute (projSet A) (measOpSet U B)) ↔ IsDeterministic U
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeterministic.commute_projSet_measOpSet_iff_isDeterministic`.

-- Generated from ChapterDeterministic.lean — theorem BookProof.ChapterDeterministic.commute_projSet_measOpSet_iff_isDeterministic
import Mathlib
import Definitions.Def_ChapterDeterministic
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterReconstruct
import Definitions.Def_ChapterTimeTranslation
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterReconstruct
open BookProof.ChapterTimeTranslation
open BookProof.ChapterDeterministic


open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct BookProof.ChapterTimeTranslation


variable {n : ℕ}

theorem BookProof.ChapterDeterministic.commute_projSet_measOpSet_iff_isDeterministic
    (U : Matrix (Fin n) (Fin n) ℂ) :
    (∀ A B : Finset (Fin n), Commute (projSet A) (measOpSet U B)) ↔ IsDeterministic U := by sorry

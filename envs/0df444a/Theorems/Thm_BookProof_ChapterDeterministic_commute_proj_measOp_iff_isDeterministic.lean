-- Prove2me | Theorems.Thm_BookProof_ChapterDeterministic_commute_proj_measOp_iff_isDeterministic
-- name    : BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:21:31.7496+00:00
-- url     : https://prove2.me/theorems/a9b280ba-1d79-4d43-82c1-f87798e1355c
-- title:
--   `BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministic` (U : Matrix (Fin n) (Fin n) ℂ) : (∀ a b : Fin n, Commute (proj a) (measOp U b)) ↔ IsDeterministic U
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeterministic`.
--
--   `BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministic` (U : Matrix (Fin n) (Fin n) ℂ) : (∀ a b : Fin n, Commute (proj a) (measOp U b)) ↔ IsDeterministic U
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministic`.

-- Generated from ChapterDeterministic.lean — theorem BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministic
import Mathlib
import Definitions.Def_ChapterDeterministic
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterReconstruct
import Definitions.Def_ChapterTimeTranslation
open BookProof.ChapterReconstruct
open BookProof.ChapterTimeTranslation
open BookProof.ChapterDeterministic


open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct BookProof.ChapterTimeTranslation


variable {n : ℕ}

theorem BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministic
    (U : Matrix (Fin n) (Fin n) ℂ) :
    (∀ a b : Fin n, Commute (proj a) (measOp U b)) ↔ IsDeterministic U := by sorry

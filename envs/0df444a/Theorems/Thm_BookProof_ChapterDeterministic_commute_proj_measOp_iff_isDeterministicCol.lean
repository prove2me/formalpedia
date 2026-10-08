-- Prove2me | Theorems.Thm_BookProof_ChapterDeterministic_commute_proj_measOp_iff_isDeterministicCol
-- name    : BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministicCol
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:21:15.552279+00:00
-- url     : https://prove2.me/theorems/493cec95-b107-4eeb-bbe9-a67fdb2b9184
-- title:
--   `BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministicCol` (U : Matrix (Fin n) (Fin n) ℂ) (b : Fin n) : (∀ a : Fin n, Commute (proj a) (measOp U b)) ↔ IsDeterminis
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeterministic`.
--
--   `BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministicCol` (U : Matrix (Fin n) (Fin n) ℂ) (b : Fin n) : (∀ a : Fin n, Commute (proj a) (measOp U b)) ↔ IsDeterministicCol U b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministicCol`.

-- Generated from ChapterDeterministic.lean — theorem BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministicCol
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

theorem BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministicCol
    (U : Matrix (Fin n) (Fin n) ℂ) (b : Fin n) :
    (∀ a : Fin n, Commute (proj a) (measOp U b)) ↔ IsDeterministicCol U b := by sorry

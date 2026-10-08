-- Prove2me | Theorems.Thm_BookProof_ChapterDeterministic_measOpSet_eq_sum
-- name    : BookProof.ChapterDeterministic.measOpSet_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:21:49.221181+00:00
-- url     : https://prove2.me/theorems/9f624bfa-c208-46f5-8efc-c53581393789
-- title:
--   `BookProof.ChapterDeterministic.measOpSet_eq_sum` (U : Matrix (Fin n) (Fin n) ℂ) (B : Finset (Fin n)) : measOpSet U B = ∑ b ∈ B, measOp U b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeterministic`.
--
--   `BookProof.ChapterDeterministic.measOpSet_eq_sum` (U : Matrix (Fin n) (Fin n) ℂ) (B : Finset (Fin n)) : measOpSet U B = ∑ b ∈ B, measOp U b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeterministic.measOpSet_eq_sum`.

-- Generated from ChapterDeterministic.lean — theorem BookProof.ChapterDeterministic.measOpSet_eq_sum
import Definitions.Def_ChapterReconstruct
import Mathlib
import Definitions.Def_ChapterDeterministic
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterTimeTranslation
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterTimeTranslation
open BookProof.ChapterDeterministic


open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct BookProof.ChapterTimeTranslation


variable {n : ℕ}

theorem BookProof.ChapterDeterministic.measOpSet_eq_sum (U : Matrix (Fin n) (Fin n) ℂ) (B : Finset (Fin n)) :
    measOpSet U B = ∑ b ∈ B, measOp U b := by sorry

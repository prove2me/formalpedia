-- Prove2me | Theorems.Thm_BookProof_ChapterDeterministic_measOp_mul_proj_apply
-- name    : BookProof.ChapterDeterministic.measOp_mul_proj_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:21:07.021071+00:00
-- url     : https://prove2.me/theorems/2470a289-cfbc-4815-afe3-fcf9bcd2a555
-- title:
--   `BookProof.ChapterDeterministic.measOp_mul_proj_apply` (U : Matrix (Fin n) (Fin n) ℂ) (a b i j : Fin n) : (measOp U b * proj a) i j = if j = a then U i b * (starRingEnd ℂ) (U a b)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeterministic`.
--
--   `BookProof.ChapterDeterministic.measOp_mul_proj_apply` (U : Matrix (Fin n) (Fin n) ℂ) (a b i j : Fin n) : (measOp U b * proj a) i j = if j = a then U i b * (starRingEnd ℂ) (U a b) else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeterministic.measOp_mul_proj_apply`.

-- Generated from ChapterDeterministic.lean — theorem BookProof.ChapterDeterministic.measOp_mul_proj_apply
import Definitions.Def_ChapterReconstruct
import Mathlib
import Definitions.Def_ChapterDeterministic
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterTimeTranslation
open BookProof.ChapterTimeTranslation
open BookProof.ChapterDeterministic


open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct BookProof.ChapterTimeTranslation


variable {n : ℕ}

theorem BookProof.ChapterDeterministic.measOp_mul_proj_apply (U : Matrix (Fin n) (Fin n) ℂ) (a b i j : Fin n) :
    (measOp U b * proj a) i j =
      if j = a then U i b * (starRingEnd ℂ) (U a b) else 0 := by sorry

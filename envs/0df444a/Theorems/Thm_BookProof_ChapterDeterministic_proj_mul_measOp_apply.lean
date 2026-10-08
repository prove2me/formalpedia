-- Prove2me | Theorems.Thm_BookProof_ChapterDeterministic_proj_mul_measOp_apply
-- name    : BookProof.ChapterDeterministic.proj_mul_measOp_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:20:58.48325+00:00
-- url     : https://prove2.me/theorems/c3697f62-e766-4894-9070-775cd65fea5f
-- title:
--   `BookProof.ChapterDeterministic.proj_mul_measOp_apply` (U : Matrix (Fin n) (Fin n) ℂ) (a b i j : Fin n) : (proj a * measOp U b) i j = if i = a then U a b * (starRingEnd ℂ) (U j b)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeterministic`.
--
--   `BookProof.ChapterDeterministic.proj_mul_measOp_apply` (U : Matrix (Fin n) (Fin n) ℂ) (a b i j : Fin n) : (proj a * measOp U b) i j = if i = a then U a b * (starRingEnd ℂ) (U j b) else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeterministic.proj_mul_measOp_apply`.

-- Generated from ChapterDeterministic.lean — theorem BookProof.ChapterDeterministic.proj_mul_measOp_apply
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

theorem BookProof.ChapterDeterministic.proj_mul_measOp_apply (U : Matrix (Fin n) (Fin n) ℂ) (a b i j : Fin n) :
    (proj a * measOp U b) i j =
      if i = a then U a b * (starRingEnd ℂ) (U j b) else 0 := by sorry

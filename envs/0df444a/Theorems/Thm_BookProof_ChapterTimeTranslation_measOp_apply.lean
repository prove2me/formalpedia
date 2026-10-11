-- Prove2me | Theorems.Thm_BookProof_ChapterTimeTranslation_measOp_apply
-- name    : BookProof.ChapterTimeTranslation.measOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:25:06.490599+00:00
-- url     : https://prove2.me/theorems/93d97376-e59b-46f8-93b3-b261176456d3
-- title:
--   `BookProof.ChapterTimeTranslation.measOp_apply` (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (k l : Fin n) : measOp U a k l = U k a * (starRingEnd ℂ) (U l a)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTimeTranslation`.
--
--   `BookProof.ChapterTimeTranslation.measOp_apply` (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (k l : Fin n) : measOp U a k l = U k a * (starRingEnd ℂ) (U l a)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTimeTranslation.measOp_apply`.

-- Generated from ChapterTimeTranslation.lean — theorem BookProof.ChapterTimeTranslation.measOp_apply
import Definitions.Def_ChapterReconstruct
import Mathlib
import Definitions.Def_ChapterTimeTranslation
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterTimeTranslation


open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct


variable {n : ℕ}

theorem BookProof.ChapterTimeTranslation.measOp_apply (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (k l : Fin n) :
    measOp U a k l = U k a * (starRingEnd ℂ) (U l a) := by sorry

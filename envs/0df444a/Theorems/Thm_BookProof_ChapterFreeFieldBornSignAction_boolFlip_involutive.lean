-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignAction_boolFlip_involutive
-- name    : BookProof.ChapterFreeFieldBornSignAction.boolFlip_involutive
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T07:17:22.120201+00:00
-- url     : https://prove2.me/theorems/f09af973-45ef-4653-896a-f79459e6cd73
-- title:
--   `BookProof.ChapterFreeFieldBornSignAction.boolFlip_involutive` (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) : boolFlip b (boolFlip b x) = x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignAction`.
--
--   `BookProof.ChapterFreeFieldBornSignAction.boolFlip_involutive` (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) : boolFlip b (boolFlip b x) = x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignAction.boolFlip_involutive`.

-- Generated from ChapterFreeFieldBornSignAction.lean — theorem BookProof.ChapterFreeFieldBornSignAction.boolFlip_involutive
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignAction

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge

theorem BookProof.ChapterFreeFieldBornSignAction.boolFlip_involutive (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) :
    boolFlip b (boolFlip b x) = x := by sorry

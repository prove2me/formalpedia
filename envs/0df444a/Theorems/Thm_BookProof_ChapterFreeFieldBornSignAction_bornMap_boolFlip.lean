-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignAction_bornMap_boolFlip
-- name    : BookProof.ChapterFreeFieldBornSignAction.bornMap_boolFlip
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T07:34:56.998972+00:00
-- url     : https://prove2.me/theorems/fb578bc2-491e-47eb-bc39-fa1890584d7c
-- title:
--   `BookProof.ChapterFreeFieldBornSignAction.bornMap_boolFlip` (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) : bornMap (boolFlip b x) = bornMap x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignAction`.
--
--   `BookProof.ChapterFreeFieldBornSignAction.bornMap_boolFlip` (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) : bornMap (boolFlip b x) = bornMap x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignAction.bornMap_boolFlip`.

-- Generated from ChapterFreeFieldBornSignAction.lean — theorem BookProof.ChapterFreeFieldBornSignAction.bornMap_boolFlip
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignAction

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge

theorem BookProof.ChapterFreeFieldBornSignAction.bornMap_boolFlip (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) :
    bornMap (boolFlip b x) = bornMap x := by sorry

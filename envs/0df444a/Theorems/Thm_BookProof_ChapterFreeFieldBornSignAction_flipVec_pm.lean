-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignAction_flipVec_pm
-- name    : BookProof.ChapterFreeFieldBornSignAction.flipVec_pm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T07:16:40.482992+00:00
-- url     : https://prove2.me/theorems/981702fa-b7a1-4713-afcd-6292e80cd594
-- title:
--   `BookProof.ChapterFreeFieldBornSignAction.flipVec_pm` (b : Fin n → Bool) (k : Fin n) : flipVec b k = 1 ∨ flipVec b k = -1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignAction`.
--
--   `BookProof.ChapterFreeFieldBornSignAction.flipVec_pm` (b : Fin n → Bool) (k : Fin n) : flipVec b k = 1 ∨ flipVec b k = -1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignAction.flipVec_pm`.

-- Generated from ChapterFreeFieldBornSignAction.lean — theorem BookProof.ChapterFreeFieldBornSignAction.flipVec_pm
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignAction

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge

theorem BookProof.ChapterFreeFieldBornSignAction.flipVec_pm (b : Fin n → Bool) (k : Fin n) :
    flipVec b k = 1 ∨ flipVec b k = -1 := by sorry

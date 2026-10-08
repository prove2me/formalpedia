-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignGauge_signFlip_neg_one
-- name    : BookProof.ChapterFreeFieldBornSignGauge.signFlip_neg_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:33:14.998994+00:00
-- url     : https://prove2.me/theorems/dc085868-96d0-4129-ad5f-01b97c0a76ca
-- title:
--   `BookProof.ChapterFreeFieldBornSignGauge.signFlip_neg_one` (x : EuclideanSpace ℝ (Fin n)) : signFlip (fun _ => -1) x = -x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignGauge`.
--
--   `BookProof.ChapterFreeFieldBornSignGauge.signFlip_neg_one` (x : EuclideanSpace ℝ (Fin n)) : signFlip (fun _ => -1) x = -x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignGauge.signFlip_neg_one`.

-- Generated from ChapterFreeFieldBornSignGauge.lean — theorem BookProof.ChapterFreeFieldBornSignGauge.signFlip_neg_one
import Definitions.Def_ChapterFreeFieldBorn
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignGauge

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn

theorem BookProof.ChapterFreeFieldBornSignGauge.signFlip_neg_one (x : EuclideanSpace ℝ (Fin n)) :
    signFlip (fun _ => -1) x = -x := by sorry

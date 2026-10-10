-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzTranslation_properTime_rest
-- name    : BookProof.ChapterLorentzTranslation.properTime_rest
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:45:50.957339+00:00
-- url     : https://prove2.me/theorems/ee9365cb-8c7f-45f5-a7ea-51c12d5d8837
-- title:
--   `BookProof.ChapterLorentzTranslation.properTime_rest` (x0 : ℝ) (xs : Fin 3 → ℝ) : properTime (fun _ => 0) x0 xs = x0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzTranslation`.
--
--   `BookProof.ChapterLorentzTranslation.properTime_rest` (x0 : ℝ) (xs : Fin 3 → ℝ) : properTime (fun _ => 0) x0 xs = x0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzTranslation.properTime_rest`.

-- Generated from ChapterLorentzTranslation.lean — theorem BookProof.ChapterLorentzTranslation.properTime_rest
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
open BookProof.ChapterLorentzTranslation



open scoped BigOperators

theorem BookProof.ChapterLorentzTranslation.properTime_rest (x0 : ℝ) (xs : Fin 3 → ℝ) :
    properTime (fun _ => 0) x0 xs = x0 := by sorry

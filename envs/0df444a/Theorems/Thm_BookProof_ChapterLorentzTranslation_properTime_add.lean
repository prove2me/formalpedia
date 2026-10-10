-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzTranslation_properTime_add
-- name    : BookProof.ChapterLorentzTranslation.properTime_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:45:46.351286+00:00
-- url     : https://prove2.me/theorems/94da5814-564b-433f-825d-3ecd3f2d7e3c
-- title:
--   `BookProof.ChapterLorentzTranslation.properTime_add` (w : Fin 3 → ℝ) (x0 y0 : ℝ) (xs ys : Fin 3 → ℝ) : properTime w (x0 + y0) (xs + ys) = properTime w x0 xs + properTime w y0 ys
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzTranslation`.
--
--   `BookProof.ChapterLorentzTranslation.properTime_add` (w : Fin 3 → ℝ) (x0 y0 : ℝ) (xs ys : Fin 3 → ℝ) : properTime w (x0 + y0) (xs + ys) = properTime w x0 xs + properTime w y0 ys
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzTranslation.properTime_add`.

-- Generated from ChapterLorentzTranslation.lean — theorem BookProof.ChapterLorentzTranslation.properTime_add
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
open BookProof.ChapterLorentzTranslation



open scoped BigOperators

theorem BookProof.ChapterLorentzTranslation.properTime_add (w : Fin 3 → ℝ) (x0 y0 : ℝ) (xs ys : Fin 3 → ℝ) :
    properTime w (x0 + y0) (xs + ys) = properTime w x0 xs + properTime w y0 ys := by sorry

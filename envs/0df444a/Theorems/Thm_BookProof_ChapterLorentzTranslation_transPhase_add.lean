-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzTranslation_transPhase_add
-- name    : BookProof.ChapterLorentzTranslation.transPhase_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:46:20.707635+00:00
-- url     : https://prove2.me/theorems/8ad4bd04-c3fa-4b90-8aae-0dcdf1fd7466
-- title:
--   `BookProof.ChapterLorentzTranslation.transPhase_add` (M : ℝ) (w : Fin 3 → ℝ) (x0 y0 : ℝ) (xs ys : Fin 3 → ℝ) : transPhase M w (x0 + y0) (xs + ys) = transPhase M w x0 xs * transPhas
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzTranslation`.
--
--   `BookProof.ChapterLorentzTranslation.transPhase_add` (M : ℝ) (w : Fin 3 → ℝ) (x0 y0 : ℝ) (xs ys : Fin 3 → ℝ) : transPhase M w (x0 + y0) (xs + ys) = transPhase M w x0 xs * transPhase M w y0 ys
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzTranslation.transPhase_add`.

-- Generated from ChapterLorentzTranslation.lean — theorem BookProof.ChapterLorentzTranslation.transPhase_add
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
open BookProof.ChapterLorentzTranslation



open scoped BigOperators

theorem BookProof.ChapterLorentzTranslation.transPhase_add (M : ℝ) (w : Fin 3 → ℝ) (x0 y0 : ℝ) (xs ys : Fin 3 → ℝ) :
    transPhase M w (x0 + y0) (xs + ys) = transPhase M w x0 xs * transPhase M w y0 ys := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzTranslation_transPhase_rest
-- name    : BookProof.ChapterLorentzTranslation.transPhase_rest
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:46:37.800154+00:00
-- url     : https://prove2.me/theorems/faeb5d01-6e28-470c-81bd-89d1477608f2
-- title:
--   `BookProof.ChapterLorentzTranslation.transPhase_rest` (M : ℝ) (x0 : ℝ) (xs : Fin 3 → ℝ) : transPhase M (fun _ => 0) x0 xs = Complex.exp (Complex.I * (M : ℂ) * (x0 : ℂ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzTranslation`.
--
--   `BookProof.ChapterLorentzTranslation.transPhase_rest` (M : ℝ) (x0 : ℝ) (xs : Fin 3 → ℝ) : transPhase M (fun _ => 0) x0 xs = Complex.exp (Complex.I * (M : ℂ) * (x0 : ℂ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzTranslation.transPhase_rest`.

-- Generated from ChapterLorentzTranslation.lean — theorem BookProof.ChapterLorentzTranslation.transPhase_rest
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
open BookProof.ChapterLorentzTranslation



open scoped BigOperators

theorem BookProof.ChapterLorentzTranslation.transPhase_rest (M : ℝ) (x0 : ℝ) (xs : Fin 3 → ℝ) :
    transPhase M (fun _ => 0) x0 xs = Complex.exp (Complex.I * (M : ℂ) * (x0 : ℂ)) := by sorry

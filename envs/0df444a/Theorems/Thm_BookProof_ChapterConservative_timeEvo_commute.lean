-- Prove2me | Theorems.Thm_BookProof_ChapterConservative_timeEvo_commute
-- name    : BookProof.ChapterConservative.timeEvo_commute
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:59:33.394977+00:00
-- url     : https://prove2.me/theorems/aedb0e44-e0ac-4b94-8598-ef46ce99e00e
-- title:
--   `BookProof.ChapterConservative.timeEvo_commute` (H : Matrix n n ℂ) (s t : ℝ) : Commute ((s : ℂ) • (Complex.I • H)) ((t : ℂ) • (Complex.I • H))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConservative`.
--
--   `BookProof.ChapterConservative.timeEvo_commute` (H : Matrix n n ℂ) (s t : ℝ) : Commute ((s : ℂ) • (Complex.I • H)) ((t : ℂ) • (Complex.I • H))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConservative.timeEvo_commute`.

-- Generated from ChapterConservative.lean — theorem BookProof.ChapterConservative.timeEvo_commute
import Mathlib
import Definitions.Def_ChapterConservative
open BookProof.ChapterConservative


open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ChapterConservative.timeEvo_commute (H : Matrix n n ℂ) (s t : ℝ) :
    Commute ((s : ℂ) • (Complex.I • H)) ((t : ℂ) • (Complex.I • H)) := by sorry

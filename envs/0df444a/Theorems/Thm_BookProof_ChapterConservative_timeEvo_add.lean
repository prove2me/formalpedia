-- Prove2me | Theorems.Thm_BookProof_ChapterConservative_timeEvo_add
-- name    : BookProof.ChapterConservative.timeEvo_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:51:45.730437+00:00
-- url     : https://prove2.me/theorems/bb774b19-1d32-41f2-b080-a8fb01a6063c
-- title:
--   `BookProof.ChapterConservative.timeEvo_add` (H : Matrix n n ℂ) (s t : ℝ) : timeEvo H s * timeEvo H t = timeEvo H (s + t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConservative`.
--
--   `BookProof.ChapterConservative.timeEvo_add` (H : Matrix n n ℂ) (s t : ℝ) : timeEvo H s * timeEvo H t = timeEvo H (s + t)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConservative.timeEvo_add`.

-- Generated from ChapterConservative.lean — theorem BookProof.ChapterConservative.timeEvo_add
import Mathlib
import Definitions.Def_ChapterConservative
open BookProof.ChapterConservative


open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ChapterConservative.timeEvo_add (H : Matrix n n ℂ) (s t : ℝ) :
    timeEvo H s * timeEvo H t = timeEvo H (s + t) := by sorry

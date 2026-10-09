-- Prove2me | Theorems.Thm_BookProof_ChapterConservative_timeEvo_inv
-- name    : BookProof.ChapterConservative.timeEvo_inv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:22:01.085513+00:00
-- url     : https://prove2.me/theorems/26ace031-ead0-4c65-983f-a9baba55b33d
-- title:
--   `BookProof.ChapterConservative.timeEvo_inv` (H : Matrix n n ℂ) (t : ℝ) : timeEvo H t * timeEvo H (-t) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConservative`.
--
--   `BookProof.ChapterConservative.timeEvo_inv` (H : Matrix n n ℂ) (t : ℝ) : timeEvo H t * timeEvo H (-t) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConservative.timeEvo_inv`.

-- Generated from ChapterConservative.lean — theorem BookProof.ChapterConservative.timeEvo_inv
import Mathlib
import Definitions.Def_ChapterConservative
open BookProof.ChapterConservative


open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ChapterConservative.timeEvo_inv (H : Matrix n n ℂ) (t : ℝ) :
    timeEvo H t * timeEvo H (-t) = 1 := by sorry

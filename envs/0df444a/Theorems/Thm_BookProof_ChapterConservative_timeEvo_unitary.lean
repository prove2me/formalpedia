-- Prove2me | Theorems.Thm_BookProof_ChapterConservative_timeEvo_unitary
-- name    : BookProof.ChapterConservative.timeEvo_unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:59:40.934999+00:00
-- url     : https://prove2.me/theorems/4139f1d3-9828-4d14-992e-809de0ab9572
-- title:
--   `BookProof.ChapterConservative.timeEvo_unitary` (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) : (timeEvo H t)ᴴ * (timeEvo H t) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConservative`.
--
--   `BookProof.ChapterConservative.timeEvo_unitary` (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) : (timeEvo H t)ᴴ * (timeEvo H t) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConservative.timeEvo_unitary`.

-- Generated from ChapterConservative.lean — theorem BookProof.ChapterConservative.timeEvo_unitary
import Mathlib
import Definitions.Def_ChapterConservative
open BookProof.ChapterConservative


open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ChapterConservative.timeEvo_unitary (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (timeEvo H t)ᴴ * (timeEvo H t) = 1 := by sorry

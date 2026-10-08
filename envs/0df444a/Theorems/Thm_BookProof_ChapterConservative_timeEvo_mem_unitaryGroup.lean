-- Prove2me | Theorems.Thm_BookProof_ChapterConservative_timeEvo_mem_unitaryGroup
-- name    : BookProof.ChapterConservative.timeEvo_mem_unitaryGroup
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:51:03.693294+00:00
-- url     : https://prove2.me/theorems/19760420-58f7-4483-b7b2-0a0f029e0088
-- title:
--   `BookProof.ChapterConservative.timeEvo_mem_unitaryGroup` (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) : timeEvo H t ∈ Matrix.unitaryGroup n ℂ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConservative`.
--
--   `BookProof.ChapterConservative.timeEvo_mem_unitaryGroup` (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) : timeEvo H t ∈ Matrix.unitaryGroup n ℂ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConservative.timeEvo_mem_unitaryGroup`.

-- Generated from ChapterConservative.lean — theorem BookProof.ChapterConservative.timeEvo_mem_unitaryGroup
import Mathlib
import Definitions.Def_ChapterConservative
open BookProof.ChapterConservative


open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ChapterConservative.timeEvo_mem_unitaryGroup (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) :
    timeEvo H t ∈ Matrix.unitaryGroup n ℂ := by sorry

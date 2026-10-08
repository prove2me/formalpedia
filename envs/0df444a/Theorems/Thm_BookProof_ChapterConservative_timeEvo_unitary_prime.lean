-- Prove2me | Theorems.Thm_BookProof_ChapterConservative_timeEvo_unitary_prime
-- name    : BookProof.ChapterConservative.timeEvo_unitary_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:59:52.270208+00:00
-- url     : https://prove2.me/theorems/df8fcb70-ce00-40d5-aae0-dc6aafdeaf49
-- title:
--   BookProof.ChapterConservative.timeEvo_unitary'
-- statement:
--   BookProof.ChapterConservative.timeEvo_unitary'

-- Generated from ChapterConservative.lean — theorem BookProof.ChapterConservative.timeEvo_unitary'
import Mathlib
import Definitions.Def_ChapterConservative
open BookProof.ChapterConservative


open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ChapterConservative.timeEvo_unitary_prime (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (timeEvo H t) * (timeEvo H t)ᴴ = 1 := by sorry

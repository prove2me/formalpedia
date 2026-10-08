-- Prove2me | Theorems.Thm_BookProof_ChapterConservative_timeEvo_conj_trace
-- name    : BookProof.ChapterConservative.timeEvo_conj_trace
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:22:18.258757+00:00
-- url     : https://prove2.me/theorems/dea009e7-3300-4a4e-b656-4c0e79435a7a
-- title:
--   `BookProof.ChapterConservative.timeEvo_conj_trace` (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) (ρ : Matrix n n ℂ) : (timeEvo H t * ρ * (timeEvo H t)ᴴ).trace = ρ.trace
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConservative`.
--
--   `BookProof.ChapterConservative.timeEvo_conj_trace` (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) (ρ : Matrix n n ℂ) : (timeEvo H t * ρ * (timeEvo H t)ᴴ).trace = ρ.trace
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterConservative.timeEvo_conj_trace`.

-- Generated from ChapterConservative.lean — theorem BookProof.ChapterConservative.timeEvo_conj_trace
import Mathlib
import Definitions.Def_ChapterConservative
open BookProof.ChapterConservative


open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ChapterConservative.timeEvo_conj_trace (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ)
    (ρ : Matrix n n ℂ) :
    (timeEvo H t * ρ * (timeEvo H t)ᴴ).trace = ρ.trace := by sorry

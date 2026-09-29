-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRestart_restart_error_accumulation_sirk
-- name    : BookProof.ChapterSirkRestart.restart_error_accumulation_sirk
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T08:02:47.143404+00:00
-- url     : https://prove2.me/theorems/15929c6c-01d1-40be-8d23-4eb8a70139ae
-- title:
--   (U S : E →L[ℂ] E) (C Dmin h : ℝ) (m : ℕ) (hU : ∀ w : E, ‖U w‖ ≤ ‖w‖) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖) (hstep : ∀ w : E, ‖U w - S w‖ ≤ sirkBound C Dmin h 1 m *...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRestart.restart_error_accumulation_sirk` (module `BookProof.ChapterSirkRestart`), source chapter `BookProof/ChapterChapterSirkRestart.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRestart.lean

-- Generated from ChapterSirkRestart.lean — theorem BookProof.ChapterSirkRestart.restart_error_accumulation_sirk
import Mathlib
import Definitions.Def_ChapterSirkRestart
open BookProof.ChapterSirkRestart







noncomputable section

open Filter Topology


open BookProof.ChapterH6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterSirkRestart.restart_error_accumulation_sirk (U S : E →L[ℂ] E) (C Dmin h : ℝ) (m : ℕ)
    (hU : ∀ w : E, ‖U w‖ ≤ ‖w‖) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖)
    (hstep : ∀ w : E, ‖U w - S w‖ ≤ sirkBound C Dmin h 1 m * ‖w‖)
    (n : ℕ) (v : E) :
    ‖(U ^ n) v - (S ^ n) v‖ ≤ n * sirkBound C Dmin h 1 m * ‖v‖ := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRestart_restart_error_accumulation
-- name    : BookProof.ChapterSirkRestart.restart_error_accumulation
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:40:26.577384+00:00
-- url     : https://prove2.me/theorems/47a1028b-1551-44e0-93ce-7c7a6d363492
-- title:
--   (U S : E →L[ℂ] E) (eps : ℝ) (hU : ∀ w : E, ‖U w‖ ≤ ‖w‖) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖) (hstep : ∀ w : E, ‖U w - S w‖ ≤ eps * ‖w‖) (n : ℕ) (v : E) : ‖(U ^ n) v - (S ^ n) v‖ ≤ n * eps * ‖v‖
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRestart.restart_error_accumulation` (module `BookProof.ChapterSirkRestart`), source chapter `BookProof/ChapterChapterSirkRestart.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRestart.lean

-- Generated from ChapterSirkRestart.lean — theorem BookProof.ChapterSirkRestart.restart_error_accumulation
import Mathlib
import Definitions.Def_ChapterSirkRestart
open BookProof.ChapterSirkRestart







noncomputable section

open Filter Topology


open BookProof.ChapterH6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterSirkRestart.restart_error_accumulation (U S : E →L[ℂ] E) (eps : ℝ)
    (hU : ∀ w : E, ‖U w‖ ≤ ‖w‖) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖)
    (hstep : ∀ w : E, ‖U w - S w‖ ≤ eps * ‖w‖)
    (n : ℕ) (v : E) :
    ‖(U ^ n) v - (S ^ n) v‖ ≤ n * eps * ‖v‖ := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRestart_restart_error_tendsto_zero
-- name    : BookProof.ChapterSirkRestart.restart_error_tendsto_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:25:21.689253+00:00
-- url     : https://prove2.me/theorems/d379f75c-c575-476a-8ef2-7e6b01818e45
-- title:
--   (C Dmin h nv : ℝ) (n : ℕ) (hh : 0 < h) : Tendsto (fun m : ℕ => (n : ℝ) * sirkBound C Dmin h nv m) atTop (𝓝 0)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRestart.restart_error_tendsto_zero` (module `BookProof.ChapterSirkRestart`), source chapter `BookProof/ChapterChapterSirkRestart.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRestart.lean

-- Generated from ChapterSirkRestart.lean — theorem BookProof.ChapterSirkRestart.restart_error_tendsto_zero
import Mathlib
import Definitions.Def_ChapterSirkRestart
open BookProof.ChapterSirkRestart







noncomputable section

open Filter Topology


open BookProof.ChapterH6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterSirkRestart.restart_error_tendsto_zero (C Dmin h nv : ℝ) (n : ℕ) (hh : 0 < h) :
    Tendsto (fun m : ℕ => (n : ℝ) * sirkBound C Dmin h nv m) atTop (𝓝 0) := by sorry

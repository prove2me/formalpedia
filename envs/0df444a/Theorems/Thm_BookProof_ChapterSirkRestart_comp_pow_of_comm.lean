-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRestart_comp_pow_of_comm
-- name    : BookProof.ChapterSirkRestart.comp_pow_of_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:24:05.344598+00:00
-- url     : https://prove2.me/theorems/ad73d67c-75a8-487c-a7c9-a56fe00ffa5e
-- title:
--   (U Om : E →L[ℂ] E) (hcomm : Om.comp U = U.comp Om) (n : ℕ) : Om.comp (U ^ n) = (U ^ n).comp Om
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRestart.comp_pow_of_comm` (module `BookProof.ChapterSirkRestart`), source chapter `BookProof/ChapterChapterSirkRestart.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRestart.lean

-- Generated from ChapterSirkRestart.lean — theorem BookProof.ChapterSirkRestart.comp_pow_of_comm
import Mathlib
import Definitions.Def_ChapterSirkRestart
open BookProof.ChapterSirkRestart







noncomputable section

open Filter Topology


open BookProof.ChapterH6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterSirkRestart.comp_pow_of_comm (U Om : E →L[ℂ] E) (hcomm : Om.comp U = U.comp Om) (n : ℕ) :
    Om.comp (U ^ n) = (U ^ n).comp Om := by sorry

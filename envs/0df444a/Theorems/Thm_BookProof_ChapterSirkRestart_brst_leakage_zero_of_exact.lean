-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRestart_brst_leakage_zero_of_exact
-- name    : BookProof.ChapterSirkRestart.brst_leakage_zero_of_exact
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:39:46.713127+00:00
-- url     : https://prove2.me/theorems/9bb7e729-3511-4796-b132-056becfeff21
-- title:
--   (U Om : E →L[ℂ] E) (hcomm : Om.comp U = U.comp Om) (n : ℕ) (v : E) (hv : Om v = 0) : Om ((U ^ n) v) = 0
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRestart.brst_leakage_zero_of_exact` (module `BookProof.ChapterSirkRestart`), source chapter `BookProof/ChapterChapterSirkRestart.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRestart.lean

-- Generated from ChapterSirkRestart.lean — theorem BookProof.ChapterSirkRestart.brst_leakage_zero_of_exact
import Mathlib
import Definitions.Def_ChapterSirkRestart
open BookProof.ChapterSirkRestart







noncomputable section

open Filter Topology


open BookProof.ChapterH6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterSirkRestart.brst_leakage_zero_of_exact (U Om : E →L[ℂ] E)
    (hcomm : Om.comp U = U.comp Om) (n : ℕ) (v : E) (hv : Om v = 0) :
    Om ((U ^ n) v) = 0 := by sorry

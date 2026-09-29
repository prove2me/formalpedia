-- Prove2me | Theorems.Thm_BookProof_ChapterSirkMultiShift_mem_seqSpan
-- name    : BookProof.ChapterSirkMultiShift.mem_seqSpan
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:32:02.367586+00:00
-- url     : https://prove2.me/theorems/838aefbb-2dee-46f1-bcf0-6070ae0e6b59
-- title:
--   (u : ℕ → E) {i m : ℕ} (hi : i < m) : u i ∈ seqSpan (K
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkMultiShift.mem_seqSpan` (module `BookProof.ChapterSirkMultiShift`), source chapter `BookProof/ChapterChapterSirkMultiShift.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkMultiShift.lean

-- Generated from ChapterSirkMultiShift.lean — theorem BookProof.ChapterSirkMultiShift.mem_seqSpan
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift










noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem BookProof.ChapterSirkMultiShift.mem_seqSpan (u : ℕ → E) {i m : ℕ} (hi : i < m) :
    u i ∈ seqSpan (K := K) u m := by sorry

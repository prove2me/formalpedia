-- Prove2me | Theorems.Thm_BookProof_ChapterSirkMultiShift_pow_mem_seqSpan
-- name    : BookProof.ChapterSirkMultiShift.pow_mem_seqSpan
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:52:29.319746+00:00
-- url     : https://prove2.me/theorems/1ae1925c-1833-4a75-8e34-11da6d6fcaf7
-- title:
--   (u : ℕ → E) (hu : ∀ i, u i - (H ^ i) v ∈ krylovSpan H v i) (i : ℕ) : (H ^ i) v ∈ seqSpan (K
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkMultiShift.pow_mem_seqSpan` (module `BookProof.ChapterSirkMultiShift`), source chapter `BookProof/ChapterChapterSirkMultiShift.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkMultiShift.lean

-- Generated from ChapterSirkMultiShift.lean — theorem BookProof.ChapterSirkMultiShift.pow_mem_seqSpan
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift










noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterSirkMultiShift.pow_mem_seqSpan (u : ℕ → E)
    (hu : ∀ i, u i - (H ^ i) v ∈ krylovSpan H v i) (i : ℕ) :
    (H ^ i) v ∈ seqSpan (K := K) u (i + 1) := by sorry

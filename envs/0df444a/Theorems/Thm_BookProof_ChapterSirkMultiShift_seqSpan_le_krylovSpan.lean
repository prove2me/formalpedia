-- Prove2me | Theorems.Thm_BookProof_ChapterSirkMultiShift_seqSpan_le_krylovSpan
-- name    : BookProof.ChapterSirkMultiShift.seqSpan_le_krylovSpan
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:34:41.766668+00:00
-- url     : https://prove2.me/theorems/f8b10b37-e16b-4cb3-b665-5dbc5433b7b2
-- title:
--   (u : ℕ → E) (hu : ∀ i, u i - (H ^ i) v ∈ krylovSpan H v i) (m : ℕ) : seqSpan (K
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkMultiShift.seqSpan_le_krylovSpan` (module `BookProof.ChapterSirkMultiShift`), source chapter `BookProof/ChapterChapterSirkMultiShift.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkMultiShift.lean

-- Generated from ChapterSirkMultiShift.lean — theorem BookProof.ChapterSirkMultiShift.seqSpan_le_krylovSpan
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift










noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterSirkMultiShift.seqSpan_le_krylovSpan (u : ℕ → E)
    (hu : ∀ i, u i - (H ^ i) v ∈ krylovSpan H v i) (m : ℕ) :
    seqSpan (K := K) u m ≤ krylovSpan H v m := by sorry

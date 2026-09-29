-- Prove2me | Theorems.Thm_BookProof_ChapterSirkMultiShift_triangularSpan_eq_krylovSpan
-- name    : BookProof.ChapterSirkMultiShift.triangularSpan_eq_krylovSpan
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:56:31.363494+00:00
-- url     : https://prove2.me/theorems/0a5770eb-34c1-4185-a192-a2e958fd8ff3
-- title:
--   (u : ℕ → E) (hu : ∀ i, u i - (H ^ i) v ∈ krylovSpan H v i) (m : ℕ) : seqSpan (K
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkMultiShift.triangularSpan_eq_krylovSpan` (module `BookProof.ChapterSirkMultiShift`), source chapter `BookProof/ChapterChapterSirkMultiShift.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkMultiShift.lean

-- Generated from ChapterSirkMultiShift.lean — theorem BookProof.ChapterSirkMultiShift.triangularSpan_eq_krylovSpan
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift










noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterSirkMultiShift.triangularSpan_eq_krylovSpan (u : ℕ → E)
    (hu : ∀ i, u i - (H ^ i) v ∈ krylovSpan H v i) (m : ℕ) :
    seqSpan (K := K) u m = krylovSpan H v m := by sorry

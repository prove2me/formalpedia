-- Prove2me | Theorems.Thm_BookProof_ChapterSirkMultiShift_multiShiftSeq_sub_pow_mem
-- name    : BookProof.ChapterSirkMultiShift.multiShiftSeq_sub_pow_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:51:50.729575+00:00
-- url     : https://prove2.me/theorems/887c7e6a-bc6d-4e02-a4cc-2b539ff80dc4
-- title:
--   (H : E →ₗ[K] E) (z : ℕ → K) (v : E) (k : ℕ) : multiShiftSeq H z v k - (H ^ k) v ∈ krylovSpan H v k
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkMultiShift.multiShiftSeq_sub_pow_mem` (module `BookProof.ChapterSirkMultiShift`), source chapter `BookProof/ChapterChapterSirkMultiShift.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkMultiShift.lean

-- Generated from ChapterSirkMultiShift.lean — theorem BookProof.ChapterSirkMultiShift.multiShiftSeq_sub_pow_mem
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift










noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterSirkMultiShift.multiShiftSeq_sub_pow_mem (H : E →ₗ[K] E) (z : ℕ → K) (v : E) (k : ℕ) :
    multiShiftSeq H z v k - (H ^ k) v ∈ krylovSpan H v k := by sorry

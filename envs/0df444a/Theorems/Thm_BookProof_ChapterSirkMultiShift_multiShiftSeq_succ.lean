-- Prove2me | Theorems.Thm_BookProof_ChapterSirkMultiShift_multiShiftSeq_succ
-- name    : BookProof.ChapterSirkMultiShift.multiShiftSeq_succ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:33:26.184985+00:00
-- url     : https://prove2.me/theorems/6f14733a-bf3a-4dce-89dc-3bf0ca7893ab
-- title:
--   (H : E →ₗ[K] E) (z : ℕ → K) (v : E) (k : ℕ) : multiShiftSeq H z v (k + 1) = H (multiShiftSeq H z v k) - z k • multiShiftSeq H z v k
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkMultiShift.multiShiftSeq_succ` (module `BookProof.ChapterSirkMultiShift`), source chapter `BookProof/ChapterChapterSirkMultiShift.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkMultiShift.lean

-- Generated from ChapterSirkMultiShift.lean — theorem BookProof.ChapterSirkMultiShift.multiShiftSeq_succ
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift










noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterSirkMultiShift.multiShiftSeq_succ (H : E →ₗ[K] E) (z : ℕ → K) (v : E) (k : ℕ) :
    multiShiftSeq H z v (k + 1) = H (multiShiftSeq H z v k) - z k • multiShiftSeq H z v k := by sorry

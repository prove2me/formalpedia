-- Prove2me | Theorems.Thm_BookProof_ChapterSirkMultiShift_multiShiftSeq_const
-- name    : BookProof.ChapterSirkMultiShift.multiShiftSeq_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:32:44.395981+00:00
-- url     : https://prove2.me/theorems/dd3d9977-95ee-4c89-8efb-9ea9f416e131
-- title:
--   (H : E →ₗ[K] E) (γ : K) (v : E) (k : ℕ) : multiShiftSeq H (fun _ => γ) v k = noInversionSeq H γ v k
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkMultiShift.multiShiftSeq_const` (module `BookProof.ChapterSirkMultiShift`), source chapter `BookProof/ChapterChapterSirkMultiShift.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkMultiShift.lean

-- Generated from ChapterSirkMultiShift.lean — theorem BookProof.ChapterSirkMultiShift.multiShiftSeq_const
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift










noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterSirkMultiShift.multiShiftSeq_const (H : E →ₗ[K] E) (γ : K) (v : E) (k : ℕ) :
    multiShiftSeq H (fun _ => γ) v k = noInversionSeq H γ v k := by sorry

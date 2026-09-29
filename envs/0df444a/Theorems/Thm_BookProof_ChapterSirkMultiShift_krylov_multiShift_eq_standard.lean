-- Prove2me | Theorems.Thm_BookProof_ChapterSirkMultiShift_krylov_multiShift_eq_standard
-- name    : BookProof.ChapterSirkMultiShift.krylov_multiShift_eq_standard
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:59:18.398979+00:00
-- url     : https://prove2.me/theorems/6f80b049-2dbf-4faf-b05a-37dfa885c0ed
-- title:
--   (H : E →ₗ[K] E) (z : ℕ → K) (v : E) (m : ℕ) : Submodule.span K {x | ∃ i < m, x = multiShiftSeq H z v i} = krylovSpan H v m
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkMultiShift.krylov_multiShift_eq_standard` (module `BookProof.ChapterSirkMultiShift`), source chapter `BookProof/ChapterChapterSirkMultiShift.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkMultiShift.lean

-- Generated from ChapterSirkMultiShift.lean — theorem BookProof.ChapterSirkMultiShift.krylov_multiShift_eq_standard
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift










noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterSirkMultiShift.krylov_multiShift_eq_standard (H : E →ₗ[K] E) (z : ℕ → K) (v : E) (m : ℕ) :
    Submodule.span K {x | ∃ i < m, x = multiShiftSeq H z v i} = krylovSpan H v m := by sorry

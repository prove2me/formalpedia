-- Prove2me | Theorems.Thm_BookProof_ChapterSirkMultiShift_krylov_multiShift_span_eq_of_shifts
-- name    : BookProof.ChapterSirkMultiShift.krylov_multiShift_span_eq_of_shifts
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T06:01:14.642891+00:00
-- url     : https://prove2.me/theorems/19f1ec65-35ee-4d5f-a111-aaa50e4bc190
-- title:
--   (H : E →ₗ[K] E) (z z' : ℕ → K) (v : E) (m : ℕ) : Submodule.span K {x | ∃ i < m, x = multiShiftSeq H z v i} = Submodule.span K {x | ∃ i < m, x = multiShiftSeq H z' v i}
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkMultiShift.krylov_multiShift_span_eq_of_shifts` (module `BookProof.ChapterSirkMultiShift`), source chapter `BookProof/ChapterChapterSirkMultiShift.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkMultiShift.lean

-- Generated from ChapterSirkMultiShift.lean — theorem BookProof.ChapterSirkMultiShift.krylov_multiShift_span_eq_of_shifts
import Mathlib
import Definitions.Def_ChapterSirkMultiShift
open BookProof.ChapterSirkMultiShift










noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterSirkMultiShift.krylov_multiShift_span_eq_of_shifts (H : E →ₗ[K] E) (z z' : ℕ → K) (v : E) (m : ℕ) :
    Submodule.span K {x | ∃ i < m, x = multiShiftSeq H z v i}
      = Submodule.span K {x | ∃ i < m, x = multiShiftSeq H z' v i} := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterH5_krylovSpan_shift_eq
-- name    : BookProof.ChapterH5.krylovSpan_shift_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:46:56.118607+00:00
-- url     : https://prove2.me/theorems/6ba73c3a-82cf-4bbc-8a25-dca34693d632
-- title:
--   `BookProof.ChapterH5.krylovSpan_shift_eq` (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) : krylovSpan (H - γ • 1) v m = krylovSpan H v m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH5`.
--
--   `BookProof.ChapterH5.krylovSpan_shift_eq` (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) : krylovSpan (H - γ • 1) v m = krylovSpan H v m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH5.krylovSpan_shift_eq`.

-- Generated from ChapterH5.lean — theorem BookProof.ChapterH5.krylovSpan_shift_eq
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5


noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterH5.krylovSpan_shift_eq (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) :
    krylovSpan (H - γ • 1) v m = krylovSpan H v m := by sorry

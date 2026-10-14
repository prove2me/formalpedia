-- Prove2me | Theorems.Thm_BookProof_ChapterH5_krylovSpan_shift_le
-- name    : BookProof.ChapterH5.krylovSpan_shift_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:47:44.033911+00:00
-- url     : https://prove2.me/theorems/7dd9a0a2-0f86-47d1-aeb4-c340596a4687
-- title:
--   `BookProof.ChapterH5.krylovSpan_shift_le` (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) : krylovSpan (H - γ • 1) v m ≤ krylovSpan H v m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH5`.
--
--   `BookProof.ChapterH5.krylovSpan_shift_le` (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) : krylovSpan (H - γ • 1) v m ≤ krylovSpan H v m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH5.krylovSpan_shift_le`.

-- Generated from ChapterH5.lean — theorem BookProof.ChapterH5.krylovSpan_shift_le
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5


noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterH5.krylovSpan_shift_le (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) :
    krylovSpan (H - γ • 1) v m ≤ krylovSpan H v m := by sorry

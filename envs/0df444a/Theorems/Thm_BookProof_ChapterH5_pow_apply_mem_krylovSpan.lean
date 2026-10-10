-- Prove2me | Theorems.Thm_BookProof_ChapterH5_pow_apply_mem_krylovSpan
-- name    : BookProof.ChapterH5.pow_apply_mem_krylovSpan
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:53:29.076851+00:00
-- url     : https://prove2.me/theorems/bac85604-b355-49df-9005-7ba38d44c30e
-- title:
--   `BookProof.ChapterH5.pow_apply_mem_krylovSpan` {i m : ℕ} (hi : i < m) : (H ^ i) v ∈ krylovSpan H v m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH5`.
--
--   `BookProof.ChapterH5.pow_apply_mem_krylovSpan` {i m : ℕ} (hi : i < m) : (H ^ i) v ∈ krylovSpan H v m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH5.pow_apply_mem_krylovSpan`.

-- Generated from ChapterH5.lean — theorem BookProof.ChapterH5.pow_apply_mem_krylovSpan
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5


noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterH5.pow_apply_mem_krylovSpan {i m : ℕ} (hi : i < m) :
    (H ^ i) v ∈ krylovSpan H v m := by sorry

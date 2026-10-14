-- Prove2me | Theorems.Thm_BookProof_ChapterH5_shift_pow_sub_pow_mem
-- name    : BookProof.ChapterH5.shift_pow_sub_pow_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:46:45.840892+00:00
-- url     : https://prove2.me/theorems/c12a975b-0628-4301-abe1-d32079bc0f99
-- title:
--   `BookProof.ChapterH5.shift_pow_sub_pow_mem` (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) : (((H - γ • 1) ^ m) v) - ((H ^ m) v) ∈ krylovSpan H v m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH5`.
--
--   `BookProof.ChapterH5.shift_pow_sub_pow_mem` (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) : (((H - γ • 1) ^ m) v) - ((H ^ m) v) ∈ krylovSpan H v m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH5.shift_pow_sub_pow_mem`.

-- Generated from ChapterH5.lean — theorem BookProof.ChapterH5.shift_pow_sub_pow_mem
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5


noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterH5.shift_pow_sub_pow_mem (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) :
    (((H - γ • 1) ^ m) v) - ((H ^ m) v) ∈ krylovSpan H v m := by sorry

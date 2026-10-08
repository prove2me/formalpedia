-- Prove2me | Theorems.Thm_BookProof_ChapterEulerNState_sum_cos_tail
-- name    : BookProof.ChapterEulerNState.sum_cos_tail
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:32:14.431985+00:00
-- url     : https://prove2.me/theorems/3ca74a59-153f-4870-a7d0-57bbafb9d3d5
-- title:
--   `BookProof.ChapterEulerNState.sum_cos_tail` (θ : ℕ → ℝ) (m : ℕ) : ∑ k ∈ Finset.range m, tailProd θ k * Real.cos (θ k) ^ 2 = 1 - tailProd θ m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerNState`.
--
--   `BookProof.ChapterEulerNState.sum_cos_tail` (θ : ℕ → ℝ) (m : ℕ) : ∑ k ∈ Finset.range m, tailProd θ k * Real.cos (θ k) ^ 2 = 1 - tailProd θ m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerNState.sum_cos_tail`.

-- Generated from ChapterEulerNState.lean — theorem BookProof.ChapterEulerNState.sum_cos_tail
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState


open scoped BigOperators

theorem BookProof.ChapterEulerNState.sum_cos_tail (θ : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, tailProd θ k * Real.cos (θ k) ^ 2
      = 1 - tailProd θ m := by sorry

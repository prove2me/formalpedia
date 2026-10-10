-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_sum_one
-- name    : BookProof.ChapterAttentionMasking.maskedSoftmax_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:29:22.508984+00:00
-- url     : https://prove2.me/theorems/6f348cbf-984d-46bb-a79c-b8d73ff6eca8
-- title:
--   `BookProof.ChapterAttentionMasking.maskedSoftmax_sum_one` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) : ∑ j, maskedSoftmax beta s S j = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMasking`.
--
--   `BookProof.ChapterAttentionMasking.maskedSoftmax_sum_one` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) : ∑ j, maskedSoftmax beta s S j = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMasking.maskedSoftmax_sum_one`.

-- Generated from ChapterAttentionMasking.lean — theorem BookProof.ChapterAttentionMasking.maskedSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMasking
open BookProof.ChapterAttentionMasking


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMasking.maskedSoftmax_sum_one (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    (hS : S.Nonempty) : ∑ j, maskedSoftmax beta s S j = 1 := by sorry

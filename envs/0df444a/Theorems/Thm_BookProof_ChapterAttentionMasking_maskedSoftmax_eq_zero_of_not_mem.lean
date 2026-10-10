-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_eq_zero_of_not_mem
-- name    : BookProof.ChapterAttentionMasking.maskedSoftmax_eq_zero_of_not_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:29:11.499981+00:00
-- url     : https://prove2.me/theorems/696f4038-d181-4f04-8917-319e621cb021
-- title:
--   `BookProof.ChapterAttentionMasking.maskedSoftmax_eq_zero_of_not_mem` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} {j : Fin m} (hj : j ∉ S) : maskedSoftmax beta s S j = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMasking`.
--
--   `BookProof.ChapterAttentionMasking.maskedSoftmax_eq_zero_of_not_mem` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} {j : Fin m} (hj : j ∉ S) : maskedSoftmax beta s S j = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMasking.maskedSoftmax_eq_zero_of_not_mem`.

-- Generated from ChapterAttentionMasking.lean — theorem BookProof.ChapterAttentionMasking.maskedSoftmax_eq_zero_of_not_mem
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMasking
open BookProof.ChapterAttentionMasking


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMasking.maskedSoftmax_eq_zero_of_not_mem (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    {j : Fin m} (hj : j ∉ S) : maskedSoftmax beta s S j = 0 := by sorry

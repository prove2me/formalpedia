-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_eq_conditional
-- name    : BookProof.ChapterAttentionMasking.maskedSoftmax_eq_conditional
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:29:39.669966+00:00
-- url     : https://prove2.me/theorems/c30eef8e-e03c-43ce-8020-197b59aefab4
-- title:
--   `BookProof.ChapterAttentionMasking.maskedSoftmax_eq_conditional` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} {j : Fin m} (hj : j ∈ S) : maskedSoftmax beta s S j = scoreSoftmax
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMasking`.
--
--   `BookProof.ChapterAttentionMasking.maskedSoftmax_eq_conditional` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} {j : Fin m} (hj : j ∈ S) : maskedSoftmax beta s S j = scoreSoftmax beta s j / ∑ l ∈ S, scoreSoftmax beta s l
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMasking.maskedSoftmax_eq_conditional`.

-- Generated from ChapterAttentionMasking.lean — theorem BookProof.ChapterAttentionMasking.maskedSoftmax_eq_conditional
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMasking
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionMasking


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMasking.maskedSoftmax_eq_conditional (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    {j : Fin m} (hj : j ∈ S) :
    maskedSoftmax beta s S j = scoreSoftmax beta s j / ∑ l ∈ S, scoreSoftmax beta s l := by sorry

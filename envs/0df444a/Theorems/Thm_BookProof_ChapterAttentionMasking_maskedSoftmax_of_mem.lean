-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_of_mem
-- name    : BookProof.ChapterAttentionMasking.maskedSoftmax_of_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:28:48.014987+00:00
-- url     : https://prove2.me/theorems/8b10a9bf-ee89-4663-a184-14dd5ac8baef
-- title:
--   `BookProof.ChapterAttentionMasking.maskedSoftmax_of_mem` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} {j : Fin m} (hj : j ∈ S) : maskedSoftmax beta s S j = Real.exp (beta * s j)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMasking`.
--
--   `BookProof.ChapterAttentionMasking.maskedSoftmax_of_mem` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} {j : Fin m} (hj : j ∈ S) : maskedSoftmax beta s S j = Real.exp (beta * s j) / ∑ l ∈ S, Real.exp (beta * s l)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMasking.maskedSoftmax_of_mem`.

-- Generated from ChapterAttentionMasking.lean — theorem BookProof.ChapterAttentionMasking.maskedSoftmax_of_mem
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMasking
open BookProof.ChapterAttentionMasking


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMasking.maskedSoftmax_of_mem (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} {j : Fin m}
    (hj : j ∈ S) :
    maskedSoftmax beta s S j = Real.exp (beta * s j) / ∑ l ∈ S, Real.exp (beta * s l) := by sorry

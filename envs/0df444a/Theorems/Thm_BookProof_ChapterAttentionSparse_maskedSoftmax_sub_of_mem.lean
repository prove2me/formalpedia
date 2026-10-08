-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSparse_maskedSoftmax_sub_of_mem
-- name    : BookProof.ChapterAttentionSparse.maskedSoftmax_sub_of_mem
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:49:35.390778+00:00
-- url     : https://prove2.me/theorems/fa85325e-e0a8-478f-9520-9a5879205ea3
-- title:
--   `BookProof.ChapterAttentionSparse.maskedSoftmax_sub_of_mem` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} {j : Fin m} (hj : j ∈ S) : maskedSoftmax beta s S j - scoreSoftmax beta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSparse`.
--
--   `BookProof.ChapterAttentionSparse.maskedSoftmax_sub_of_mem` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} {j : Fin m} (hj : j ∈ S) : maskedSoftmax beta s S j - scoreSoftmax beta s j = scoreSoftmax beta s j * (1 - attendedMass beta s S) / attendedMass beta s S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSparse.maskedSoftmax_sub_of_mem`.

-- Generated from ChapterAttentionSparse.lean — theorem BookProof.ChapterAttentionSparse.maskedSoftmax_sub_of_mem
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionSparse
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionMasking
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSparse


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionMasking

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionSparse.maskedSoftmax_sub_of_mem (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    {j : Fin m} (hj : j ∈ S) :
    maskedSoftmax beta s S j - scoreSoftmax beta s j
      = scoreSoftmax beta s j * (1 - attendedMass beta s S) / attendedMass beta s S := by sorry

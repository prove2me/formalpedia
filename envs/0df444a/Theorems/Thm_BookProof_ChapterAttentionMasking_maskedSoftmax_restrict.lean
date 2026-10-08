-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_restrict
-- name    : BookProof.ChapterAttentionMasking.maskedSoftmax_restrict
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:29:57.799311+00:00
-- url     : https://prove2.me/theorems/48c1d9b2-7456-48cd-af26-7fd3a60894ab
-- title:
--   `BookProof.ChapterAttentionMasking.maskedSoftmax_restrict` (beta : ℝ) (s : Fin m → ℝ) {S T : Finset (Fin m)} (hTS : T ⊆ S) {j : Fin m} (hj : j ∈ T) : maskedSoftmax beta s T j = mas
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMasking`.
--
--   `BookProof.ChapterAttentionMasking.maskedSoftmax_restrict` (beta : ℝ) (s : Fin m → ℝ) {S T : Finset (Fin m)} (hTS : T ⊆ S) {j : Fin m} (hj : j ∈ T) : maskedSoftmax beta s T j = maskedSoftmax beta s S j / ∑ l ∈ T, maskedSoftmax beta s S l
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMasking.maskedSoftmax_restrict`.

-- Generated from ChapterAttentionMasking.lean — theorem BookProof.ChapterAttentionMasking.maskedSoftmax_restrict
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMasking
open BookProof.ChapterAttentionMasking


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMasking.maskedSoftmax_restrict (beta : ℝ) (s : Fin m → ℝ) {S T : Finset (Fin m)}
    (hTS : T ⊆ S) {j : Fin m} (hj : j ∈ T) :
    maskedSoftmax beta s T j
      = maskedSoftmax beta s S j / ∑ l ∈ T, maskedSoftmax beta s S l := by sorry

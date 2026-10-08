-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_le_iff
-- name    : BookProof.ChapterAttentionMasking.maskedSoftmax_le_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:29:49.198784+00:00
-- url     : https://prove2.me/theorems/67cc2e9e-589f-474c-8f92-cd212c330403
-- title:
--   `BookProof.ChapterAttentionMasking.maskedSoftmax_le_iff` {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) {S : Finset (Fin m)} {i j : Fin m} (hi : i ∈ S) (hj : j ∈ S) : maskedSoftmax
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMasking`.
--
--   `BookProof.ChapterAttentionMasking.maskedSoftmax_le_iff` {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) {S : Finset (Fin m)} {i j : Fin m} (hi : i ∈ S) (hj : j ∈ S) : maskedSoftmax beta s S i ≤ maskedSoftmax beta s S j ↔ s i ≤ s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMasking.maskedSoftmax_le_iff`.

-- Generated from ChapterAttentionMasking.lean — theorem BookProof.ChapterAttentionMasking.maskedSoftmax_le_iff
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMasking
open BookProof.ChapterAttentionMasking


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMasking.maskedSoftmax_le_iff {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ)
    {S : Finset (Fin m)} {i j : Fin m} (hi : i ∈ S) (hj : j ∈ S) :
    maskedSoftmax beta s S i ≤ maskedSoftmax beta s S j ↔ s i ≤ s j := by sorry

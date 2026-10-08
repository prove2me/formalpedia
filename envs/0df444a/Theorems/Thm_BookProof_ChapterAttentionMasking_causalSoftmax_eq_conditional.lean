-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMasking_causalSoftmax_eq_conditional
-- name    : BookProof.ChapterAttentionMasking.causalSoftmax_eq_conditional
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:30:37.142984+00:00
-- url     : https://prove2.me/theorems/52451b6e-6997-423e-9673-2f3e4e544698
-- title:
--   `BookProof.ChapterAttentionMasking.causalSoftmax_eq_conditional` (beta : ℝ) (s : Fin m → ℝ) {i j : Fin m} (hij : j ≤ i) : maskedSoftmax beta s (causalMask m i) j = scoreSoftmax bet
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMasking`.
--
--   `BookProof.ChapterAttentionMasking.causalSoftmax_eq_conditional` (beta : ℝ) (s : Fin m → ℝ) {i j : Fin m} (hij : j ≤ i) : maskedSoftmax beta s (causalMask m i) j = scoreSoftmax beta s j / ∑ l ∈ causalMask m i, scoreSoftmax beta s l
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMasking.causalSoftmax_eq_conditional`.

-- Generated from ChapterAttentionMasking.lean — theorem BookProof.ChapterAttentionMasking.causalSoftmax_eq_conditional
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

theorem BookProof.ChapterAttentionMasking.causalSoftmax_eq_conditional (beta : ℝ) (s : Fin m → ℝ) {i j : Fin m} (hij : j ≤ i) :
    maskedSoftmax beta s (causalMask m i) j
      = scoreSoftmax beta s j / ∑ l ∈ causalMask m i, scoreSoftmax beta s l := by sorry

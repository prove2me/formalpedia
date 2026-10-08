-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCollision_effectiveSupport_scoreSoftmax_zero
-- name    : BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:23:10.131984+00:00
-- url     : https://prove2.me/theorems/ce974fcd-98ed-4b0a-8633-574a58f173ef
-- title:
--   `BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_zero` (s : Fin m → ℝ) (i : Fin m) : effectiveSupport (scoreSoftmax 0 s) = (m : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCollision`.
--
--   `BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_zero` (s : Fin m → ℝ) (i : Fin m) : effectiveSupport (scoreSoftmax 0 s) = (m : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_zero`.

-- Generated from ChapterAttentionCollision.lean — theorem BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_zero
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCollision
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionCollision


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_zero (s : Fin m → ℝ) (i : Fin m) :
    effectiveSupport (scoreSoftmax 0 s) = (m : ℝ) := by sorry

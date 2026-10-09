-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionPrior_priorSoftmax_sum_one
-- name    : BookProof.ChapterAttentionPrior.priorSoftmax_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:39:21.319986+00:00
-- url     : https://prove2.me/theorems/c87cf8bd-92a6-4aba-a9c2-8a7759402e80
-- title:
--   `BookProof.ChapterAttentionPrior.priorSoftmax_sum_one` {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : ∑ j, priorSoftmax w beta s j = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionPrior`.
--
--   `BookProof.ChapterAttentionPrior.priorSoftmax_sum_one` {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : ∑ j, priorSoftmax w beta s j = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionPrior.priorSoftmax_sum_one`.

-- Generated from ChapterAttentionPrior.lean — theorem BookProof.ChapterAttentionPrior.priorSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionPrior
open BookProof.ChapterAttentionPrior


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionPrior.priorSoftmax_sum_one {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) (beta : ℝ)
    (s : Fin m → ℝ) (i : Fin m) : ∑ j, priorSoftmax w beta s j = 1 := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionPrior_priorSoftmax_zero
-- name    : BookProof.ChapterAttentionPrior.priorSoftmax_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:40:37.05143+00:00
-- url     : https://prove2.me/theorems/6d0ae006-a675-4bc2-bcdd-8a2be91ddf77
-- title:
--   `BookProof.ChapterAttentionPrior.priorSoftmax_zero` (w : Fin m → ℝ) (s : Fin m → ℝ) (j : Fin m) : priorSoftmax w 0 s j = w j / ∑ l, w l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionPrior`.
--
--   `BookProof.ChapterAttentionPrior.priorSoftmax_zero` (w : Fin m → ℝ) (s : Fin m → ℝ) (j : Fin m) : priorSoftmax w 0 s j = w j / ∑ l, w l
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionPrior.priorSoftmax_zero`.

-- Generated from ChapterAttentionPrior.lean — theorem BookProof.ChapterAttentionPrior.priorSoftmax_zero
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionPrior
open BookProof.ChapterAttentionPrior


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionPrior.priorSoftmax_zero (w : Fin m → ℝ) (s : Fin m → ℝ) (j : Fin m) :
    priorSoftmax w 0 s j = w j / ∑ l, w l := by sorry

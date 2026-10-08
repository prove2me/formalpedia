-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionPrior_priorSoftmax_smul
-- name    : BookProof.ChapterAttentionPrior.priorSoftmax_smul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:40:06.418157+00:00
-- url     : https://prove2.me/theorems/bbc79d8b-a532-4744-aaff-8c65c85f3b84
-- title:
--   `BookProof.ChapterAttentionPrior.priorSoftmax_smul` {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) {c : ℝ} (hc : 0 < c) (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : priorSoftmax (fun l => c * w l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionPrior`.
--
--   `BookProof.ChapterAttentionPrior.priorSoftmax_smul` {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) {c : ℝ} (hc : 0 < c) (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : priorSoftmax (fun l => c * w l) beta s j = priorSoftmax w beta s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionPrior.priorSoftmax_smul`.

-- Generated from ChapterAttentionPrior.lean — theorem BookProof.ChapterAttentionPrior.priorSoftmax_smul
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionPrior
open BookProof.ChapterAttentionPrior


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionPrior.priorSoftmax_smul {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) {c : ℝ} (hc : 0 < c)
    (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    priorSoftmax (fun l => c * w l) beta s j = priorSoftmax w beta s j := by sorry

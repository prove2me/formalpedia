-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionPrior_priorSoftmax_uniform
-- name    : BookProof.ChapterAttentionPrior.priorSoftmax_uniform
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:40:03.756726+00:00
-- url     : https://prove2.me/theorems/29c8534d-b4e7-48e1-8fec-7c0d94217679
-- title:
--   `BookProof.ChapterAttentionPrior.priorSoftmax_uniform` {c : ℝ} (hc : 0 < c) (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : priorSoftmax (fun _ => c) beta s j = scoreSoftmax beta s j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionPrior`.
--
--   `BookProof.ChapterAttentionPrior.priorSoftmax_uniform` {c : ℝ} (hc : 0 < c) (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : priorSoftmax (fun _ => c) beta s j = scoreSoftmax beta s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionPrior.priorSoftmax_uniform`.

-- Generated from ChapterAttentionPrior.lean — theorem BookProof.ChapterAttentionPrior.priorSoftmax_uniform
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionPrior
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionPrior


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionPrior.priorSoftmax_uniform {c : ℝ} (hc : 0 < c) (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    priorSoftmax (fun _ => c) beta s j = scoreSoftmax beta s j := by sorry

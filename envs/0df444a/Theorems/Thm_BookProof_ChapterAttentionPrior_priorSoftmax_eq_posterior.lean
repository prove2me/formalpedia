-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionPrior_priorSoftmax_eq_posterior
-- name    : BookProof.ChapterAttentionPrior.priorSoftmax_eq_posterior
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:39:30.684341+00:00
-- url     : https://prove2.me/theorems/df27de67-1384-4c73-a4a6-313683c335ea
-- title:
--   `BookProof.ChapterAttentionPrior.priorSoftmax_eq_posterior` (w : Fin m → ℝ) (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : priorSoftmax w beta s j = posterior w (fun l (_ : Unit) => Real
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionPrior`.
--
--   `BookProof.ChapterAttentionPrior.priorSoftmax_eq_posterior` (w : Fin m → ℝ) (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : priorSoftmax w beta s j = posterior w (fun l (_ : Unit) => Real.exp (beta * s l)) () j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionPrior.priorSoftmax_eq_posterior`.

-- Generated from ChapterAttentionPrior.lean — theorem BookProof.ChapterAttentionPrior.priorSoftmax_eq_posterior
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionPrior
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterAttentionPrior


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionPrior.priorSoftmax_eq_posterior (w : Fin m → ℝ) (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    priorSoftmax w beta s j
      = posterior w (fun l (_ : Unit) => Real.exp (beta * s l)) () j := by sorry

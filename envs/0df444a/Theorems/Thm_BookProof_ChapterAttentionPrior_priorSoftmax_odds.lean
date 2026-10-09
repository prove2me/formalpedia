-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionPrior_priorSoftmax_odds
-- name    : BookProof.ChapterAttentionPrior.priorSoftmax_odds
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:39:32.685524+00:00
-- url     : https://prove2.me/theorems/baa68434-2442-457f-bf6c-7322f200c0ed
-- title:
--   `BookProof.ChapterAttentionPrior.priorSoftmax_odds` {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) : priorSoftmax w beta s i = (w i / w j) * Real.exp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionPrior`.
--
--   `BookProof.ChapterAttentionPrior.priorSoftmax_odds` {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) : priorSoftmax w beta s i = (w i / w j) * Real.exp (beta * (s i - s j)) * priorSoftmax w beta s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionPrior.priorSoftmax_odds`.

-- Generated from ChapterAttentionPrior.lean — theorem BookProof.ChapterAttentionPrior.priorSoftmax_odds
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionPrior
open BookProof.ChapterAttentionPrior


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionPrior.priorSoftmax_odds {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) (beta : ℝ) (s : Fin m → ℝ)
    (i j : Fin m) :
    priorSoftmax w beta s i
      = (w i / w j) * Real.exp (beta * (s i - s j)) * priorSoftmax w beta s j := by sorry

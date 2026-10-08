-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionPrior_priorSoftmax_eq_scoreSoftmax_bias
-- name    : BookProof.ChapterAttentionPrior.priorSoftmax_eq_scoreSoftmax_bias
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:39:32.443981+00:00
-- url     : https://prove2.me/theorems/0129ab3d-f8ff-4e3a-836b-d0b4060507ad
-- title:
--   `BookProof.ChapterAttentionPrior.priorSoftmax_eq_scoreSoftmax_bias` {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) {beta : ℝ} (hb : beta ≠ 0) (s : Fin m → ℝ) (j : Fin m) : priorSoftmax w beta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionPrior`.
--
--   `BookProof.ChapterAttentionPrior.priorSoftmax_eq_scoreSoftmax_bias` {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) {beta : ℝ} (hb : beta ≠ 0) (s : Fin m → ℝ) (j : Fin m) : priorSoftmax w beta s j = scoreSoftmax beta (fun l => s l + Real.log (w l) / beta) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionPrior.priorSoftmax_eq_scoreSoftmax_bias`.

-- Generated from ChapterAttentionPrior.lean — theorem BookProof.ChapterAttentionPrior.priorSoftmax_eq_scoreSoftmax_bias
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

theorem BookProof.ChapterAttentionPrior.priorSoftmax_eq_scoreSoftmax_bias {w : Fin m → ℝ} (hw : ∀ j, 0 < w j)
    {beta : ℝ} (hb : beta ≠ 0) (s : Fin m → ℝ) (j : Fin m) :
    priorSoftmax w beta s j
      = scoreSoftmax beta (fun l => s l + Real.log (w l) / beta) j := by sorry

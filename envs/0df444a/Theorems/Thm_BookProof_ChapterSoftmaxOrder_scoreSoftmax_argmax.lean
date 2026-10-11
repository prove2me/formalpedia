-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_argmax
-- name    : BookProof.ChapterSoftmaxOrder.scoreSoftmax_argmax
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:35:52.482244+00:00
-- url     : https://prove2.me/theorems/914da311-dfaf-4a4c-a228-a448322126ca
-- title:
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_argmax` {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) (j : Fin m) (hj : ∀ l, s l ≤ s j) (i : Fin m) : scoreSoftmax beta s i ≤ scoreSoftm
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxOrder`.
--
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_argmax` {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) (j : Fin m) (hj : ∀ l, s l ≤ s j) (i : Fin m) : scoreSoftmax beta s i ≤ scoreSoftmax beta s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxOrder.scoreSoftmax_argmax`.

-- Generated from ChapterSoftmaxOrder.lean — theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_argmax
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxOrder


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_argmax {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) (j : Fin m)
    (hj : ∀ l, s l ≤ s j) (i : Fin m) :
    scoreSoftmax beta s i ≤ scoreSoftmax beta s j := by sorry

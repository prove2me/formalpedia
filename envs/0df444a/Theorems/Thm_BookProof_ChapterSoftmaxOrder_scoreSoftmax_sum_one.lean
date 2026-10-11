-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
-- name    : BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:35:20.393046+00:00
-- url     : https://prove2.me/theorems/fb1b8629-fefd-43d8-bd0e-c3342ffa54c6
-- title:
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : ∑ j, scoreSoftmax beta s j = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxOrder`.
--
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : ∑ j, scoreSoftmax beta s j = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one`.

-- Generated from ChapterSoftmaxOrder.lean — theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one
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

theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    ∑ j, scoreSoftmax beta s j = 1 := by sorry

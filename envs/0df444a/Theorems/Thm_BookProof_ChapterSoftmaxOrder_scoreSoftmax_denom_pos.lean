-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_denom_pos
-- name    : BookProof.ChapterSoftmaxOrder.scoreSoftmax_denom_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:34:59.726989+00:00
-- url     : https://prove2.me/theorems/356fa72f-4ee5-4d7f-8040-dc050b0798bf
-- title:
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_denom_pos` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : 0 < ∑ l, Real.exp (beta * s l)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxOrder`.
--
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_denom_pos` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : 0 < ∑ l, Real.exp (beta * s l)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxOrder.scoreSoftmax_denom_pos`.

-- Generated from ChapterSoftmaxOrder.lean — theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_denom_pos
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxOrder


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_denom_pos (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    0 < ∑ l, Real.exp (beta * s l) := by sorry

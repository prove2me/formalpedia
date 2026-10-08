-- Prove2me | Theorems.Thm_BookProof_ChapterCrossEntropyGradient_crossEntropyLoss_eq_neg_log
-- name    : BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_eq_neg_log
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:24:47.000003+00:00
-- url     : https://prove2.me/theorems/c7ce1252-4e92-4d98-8fc3-213f08fca1c3
-- title:
--   `BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_eq_neg_log` (beta : ℝ) (s : Fin m → ℝ) (y : Fin m) : crossEntropyLoss beta s y = -Real.log (scoreSoftmax beta s y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCrossEntropyGradient`.
--
--   `BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_eq_neg_log` (beta : ℝ) (s : Fin m → ℝ) (y : Fin m) : crossEntropyLoss beta s y = -Real.log (scoreSoftmax beta s y)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_eq_neg_log`.

-- Generated from ChapterCrossEntropyGradient.lean — theorem BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_eq_neg_log
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterCrossEntropyGradient
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterCrossEntropyGradient


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_eq_neg_log (beta : ℝ) (s : Fin m → ℝ) (y : Fin m) :
    crossEntropyLoss beta s y = -Real.log (scoreSoftmax beta s y) := by sorry

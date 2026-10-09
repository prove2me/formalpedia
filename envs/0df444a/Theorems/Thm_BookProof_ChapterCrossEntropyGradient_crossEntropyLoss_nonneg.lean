-- Prove2me | Theorems.Thm_BookProof_ChapterCrossEntropyGradient_crossEntropyLoss_nonneg
-- name    : BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:27:34.915579+00:00
-- url     : https://prove2.me/theorems/b845866c-41f4-424c-a488-88e3f3661b8c
-- title:
--   `BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_nonneg` (beta : ℝ) (s : Fin m → ℝ) (y : Fin m) : 0 ≤ crossEntropyLoss beta s y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCrossEntropyGradient`.
--
--   `BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_nonneg` (beta : ℝ) (s : Fin m → ℝ) (y : Fin m) : 0 ≤ crossEntropyLoss beta s y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_nonneg`.

-- Generated from ChapterCrossEntropyGradient.lean — theorem BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_nonneg
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

theorem BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_nonneg (beta : ℝ) (s : Fin m → ℝ) (y : Fin m) :
    0 ≤ crossEntropyLoss beta s y := by sorry

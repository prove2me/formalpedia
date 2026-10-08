-- Prove2me | Theorems.Thm_BookProof_ChapterCrossEntropyGradient_convexOn_crossEntropyLoss
-- name    : BookProof.ChapterCrossEntropyGradient.convexOn_crossEntropyLoss
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:25:26.282664+00:00
-- url     : https://prove2.me/theorems/57937798-8a3e-4f3a-bd34-38bf39676d95
-- title:
--   `BookProof.ChapterCrossEntropyGradient.convexOn_crossEntropyLoss` (s : Fin m → ℝ) (y : Fin m) : ConvexOn ℝ Set.univ (fun b : ℝ => crossEntropyLoss b s y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCrossEntropyGradient`.
--
--   `BookProof.ChapterCrossEntropyGradient.convexOn_crossEntropyLoss` (s : Fin m → ℝ) (y : Fin m) : ConvexOn ℝ Set.univ (fun b : ℝ => crossEntropyLoss b s y)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCrossEntropyGradient.convexOn_crossEntropyLoss`.

-- Generated from ChapterCrossEntropyGradient.lean — theorem BookProof.ChapterCrossEntropyGradient.convexOn_crossEntropyLoss
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterCrossEntropyGradient
open BookProof.ChapterCrossEntropyGradient


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterCrossEntropyGradient.convexOn_crossEntropyLoss (s : Fin m → ℝ) (y : Fin m) :
    ConvexOn ℝ Set.univ (fun b : ℝ => crossEntropyLoss b s y) := by sorry

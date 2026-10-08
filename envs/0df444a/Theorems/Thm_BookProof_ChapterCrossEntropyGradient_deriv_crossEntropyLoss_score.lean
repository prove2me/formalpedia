-- Prove2me | Theorems.Thm_BookProof_ChapterCrossEntropyGradient_deriv_crossEntropyLoss_score
-- name    : BookProof.ChapterCrossEntropyGradient.deriv_crossEntropyLoss_score
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:25:03.936339+00:00
-- url     : https://prove2.me/theorems/732287d9-f958-4b8d-9f31-45a145de0ca8
-- title:
--   `BookProof.ChapterCrossEntropyGradient.deriv_crossEntropyLoss_score` (beta : ℝ) (s : Fin m → ℝ) (y i : Fin m) : deriv (fun t : ℝ => crossEntropyLoss beta (scorePerturb s i t) y) 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCrossEntropyGradient`.
--
--   `BookProof.ChapterCrossEntropyGradient.deriv_crossEntropyLoss_score` (beta : ℝ) (s : Fin m → ℝ) (y i : Fin m) : deriv (fun t : ℝ => crossEntropyLoss beta (scorePerturb s i t) y) 0 = crossEntropyGradient beta s y i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCrossEntropyGradient.deriv_crossEntropyLoss_score`.

-- Generated from ChapterCrossEntropyGradient.lean — theorem BookProof.ChapterCrossEntropyGradient.deriv_crossEntropyLoss_score
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterCrossEntropyGradient
import Definitions.Def_ChapterSoftmaxJacobian
open BookProof.ChapterCrossEntropyGradient


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxJacobian

variable {m : ℕ}

theorem BookProof.ChapterCrossEntropyGradient.deriv_crossEntropyLoss_score (beta : ℝ) (s : Fin m → ℝ) (y i : Fin m) :
    deriv (fun t : ℝ => crossEntropyLoss beta (scorePerturb s i t) y) 0
      = crossEntropyGradient beta s y i := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterCrossEntropyGradient_hasDerivAt_crossEntropyLoss_score
-- name    : BookProof.ChapterCrossEntropyGradient.hasDerivAt_crossEntropyLoss_score
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:24:45.876076+00:00
-- url     : https://prove2.me/theorems/b44d77bf-7dbc-4c99-bd98-727e9b734390
-- title:
--   `BookProof.ChapterCrossEntropyGradient.hasDerivAt_crossEntropyLoss_score` (beta : ℝ) (s : Fin m → ℝ) (y i : Fin m) : HasDerivAt (fun t : ℝ => crossEntropyLoss beta (scorePerturb s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCrossEntropyGradient`.
--
--   `BookProof.ChapterCrossEntropyGradient.hasDerivAt_crossEntropyLoss_score` (beta : ℝ) (s : Fin m → ℝ) (y i : Fin m) : HasDerivAt (fun t : ℝ => crossEntropyLoss beta (scorePerturb s i t) y) (crossEntropyGradient beta s y i) 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCrossEntropyGradient.hasDerivAt_crossEntropyLoss_score`.

-- Generated from ChapterCrossEntropyGradient.lean — theorem BookProof.ChapterCrossEntropyGradient.hasDerivAt_crossEntropyLoss_score
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterCrossEntropyGradient
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxJacobian
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterCrossEntropyGradient


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxJacobian

variable {m : ℕ}

theorem BookProof.ChapterCrossEntropyGradient.hasDerivAt_crossEntropyLoss_score (beta : ℝ) (s : Fin m → ℝ) (y i : Fin m) :
    HasDerivAt (fun t : ℝ => crossEntropyLoss beta (scorePerturb s i t) y)
      (crossEntropyGradient beta s y i) 0 := by sorry

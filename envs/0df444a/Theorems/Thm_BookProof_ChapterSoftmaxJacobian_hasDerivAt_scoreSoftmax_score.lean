-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_hasDerivAt_scoreSoftmax_score
-- name    : BookProof.ChapterSoftmaxJacobian.hasDerivAt_scoreSoftmax_score
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:16:15.881112+00:00
-- url     : https://prove2.me/theorems/ab30696c-6f07-4ffd-a76e-a182acaa59c8
-- title:
--   `BookProof.ChapterSoftmaxJacobian.hasDerivAt_scoreSoftmax_score` (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) : HasDerivAt (fun t : ℝ => scoreSoftmax beta (scorePerturb s i t) j) (soft
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.hasDerivAt_scoreSoftmax_score` (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) : HasDerivAt (fun t : ℝ => scoreSoftmax beta (scorePerturb s i t) j) (softmaxJacobian beta s i j) 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.hasDerivAt_scoreSoftmax_score`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.hasDerivAt_scoreSoftmax_score
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxJacobian


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxJacobian.hasDerivAt_scoreSoftmax_score (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) :
    HasDerivAt (fun t : ℝ => scoreSoftmax beta (scorePerturb s i t) j)
      (softmaxJacobian beta s i j) 0 := by sorry

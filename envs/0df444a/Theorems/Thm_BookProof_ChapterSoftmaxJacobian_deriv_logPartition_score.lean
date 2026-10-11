-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_deriv_logPartition_score
-- name    : BookProof.ChapterSoftmaxJacobian.deriv_logPartition_score
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T00:08:01.683312+00:00
-- url     : https://prove2.me/theorems/bc0c2558-d0d5-4a3e-817e-2223daadef53
-- title:
--   `BookProof.ChapterSoftmaxJacobian.deriv_logPartition_score` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : deriv (fun t : ℝ => logPartition beta (scorePerturb s i t)) 0 = beta * scoreSof
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.deriv_logPartition_score` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : deriv (fun t : ℝ => logPartition beta (scorePerturb s i t)) 0 = beta * scoreSoftmax beta s i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.deriv_logPartition_score`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.deriv_logPartition_score
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxJacobian


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxJacobian.deriv_logPartition_score (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    deriv (fun t : ℝ => logPartition beta (scorePerturb s i t)) 0
      = beta * scoreSoftmax beta s i := by sorry

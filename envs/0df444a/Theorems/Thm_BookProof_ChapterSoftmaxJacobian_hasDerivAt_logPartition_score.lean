-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_hasDerivAt_logPartition_score
-- name    : BookProof.ChapterSoftmaxJacobian.hasDerivAt_logPartition_score
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:18:24.618368+00:00
-- url     : https://prove2.me/theorems/82fcd0ef-d60b-41f6-8916-a30a061fe580
-- title:
--   `BookProof.ChapterSoftmaxJacobian.hasDerivAt_logPartition_score` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : HasDerivAt (fun t : ℝ => logPartition beta (scorePerturb s i t)) (beta * s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.hasDerivAt_logPartition_score` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : HasDerivAt (fun t : ℝ => logPartition beta (scorePerturb s i t)) (beta * scoreSoftmax beta s i) 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.hasDerivAt_logPartition_score`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.hasDerivAt_logPartition_score
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

theorem BookProof.ChapterSoftmaxJacobian.hasDerivAt_logPartition_score (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun t : ℝ => logPartition beta (scorePerturb s i t))
      (beta * scoreSoftmax beta s i) 0 := by sorry

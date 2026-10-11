-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_hasDerivAt_partition_score
-- name    : BookProof.ChapterSoftmaxJacobian.hasDerivAt_partition_score
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T00:08:00.177663+00:00
-- url     : https://prove2.me/theorems/156bc978-202e-4218-8035-5640e4e2e7f1
-- title:
--   `BookProof.ChapterSoftmaxJacobian.hasDerivAt_partition_score` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : HasDerivAt (fun t : ℝ => partition beta (scorePerturb s i t)) (beta * Real.ex
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.hasDerivAt_partition_score` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : HasDerivAt (fun t : ℝ => partition beta (scorePerturb s i t)) (beta * Real.exp (beta * s i)) 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.hasDerivAt_partition_score`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.hasDerivAt_partition_score
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxJacobian


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxJacobian.hasDerivAt_partition_score (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun t : ℝ => partition beta (scorePerturb s i t))
      (beta * Real.exp (beta * s i)) 0 := by sorry

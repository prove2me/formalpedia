-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_deriv_scoreSoftmax_score
-- name    : BookProof.ChapterSoftmaxJacobian.deriv_scoreSoftmax_score
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:20:43.752736+00:00
-- url     : https://prove2.me/theorems/fa8d34fb-259a-4e24-89b9-454df9f95bfb
-- title:
--   `BookProof.ChapterSoftmaxJacobian.deriv_scoreSoftmax_score` (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) : deriv (fun t : ℝ => scoreSoftmax beta (scorePerturb s i t) j) 0 = softmaxJaco
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.deriv_scoreSoftmax_score` (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) : deriv (fun t : ℝ => scoreSoftmax beta (scorePerturb s i t) j) 0 = softmaxJacobian beta s i j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.deriv_scoreSoftmax_score`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.deriv_scoreSoftmax_score
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

theorem BookProof.ChapterSoftmaxJacobian.deriv_scoreSoftmax_score (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) :
    deriv (fun t : ℝ => scoreSoftmax beta (scorePerturb s i t) j) 0
      = softmaxJacobian beta s i j := by sorry

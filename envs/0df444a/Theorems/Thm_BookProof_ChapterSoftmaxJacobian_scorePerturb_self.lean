-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_scorePerturb_self
-- name    : BookProof.ChapterSoftmaxJacobian.scorePerturb_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:17:48.435654+00:00
-- url     : https://prove2.me/theorems/1b4844c1-02e3-4aa7-a2ee-49fab2c1d4fa
-- title:
--   `BookProof.ChapterSoftmaxJacobian.scorePerturb_self` (s : Fin m → ℝ) (i : Fin m) (t : ℝ) : scorePerturb s i t i = s i + t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.scorePerturb_self` (s : Fin m → ℝ) (i : Fin m) (t : ℝ) : scorePerturb s i t i = s i + t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.scorePerturb_self`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.scorePerturb_self
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
open BookProof.ChapterSoftmaxJacobian


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxJacobian.scorePerturb_self (s : Fin m → ℝ) (i : Fin m) (t : ℝ) :
    scorePerturb s i t i = s i + t := by sorry

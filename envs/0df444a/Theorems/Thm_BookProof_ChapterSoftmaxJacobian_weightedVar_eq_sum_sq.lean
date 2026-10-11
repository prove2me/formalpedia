-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_weightedVar_eq_sum_sq
-- name    : BookProof.ChapterSoftmaxJacobian.weightedVar_eq_sum_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:34:07.013067+00:00
-- url     : https://prove2.me/theorems/6f54f16c-28d1-418e-b62e-bcca32997233
-- title:
--   `BookProof.ChapterSoftmaxJacobian.weightedVar_eq_sum_sq` (beta : ℝ) (s x : Fin m → ℝ) (i : Fin m) : weightedVar beta s x = ∑ j, scoreSoftmax beta s j * (x j - ∑ l, scoreSoftmax bet
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.weightedVar_eq_sum_sq` (beta : ℝ) (s x : Fin m → ℝ) (i : Fin m) : weightedVar beta s x = ∑ j, scoreSoftmax beta s j * (x j - ∑ l, scoreSoftmax beta s l * x l) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.weightedVar_eq_sum_sq`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.weightedVar_eq_sum_sq
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

theorem BookProof.ChapterSoftmaxJacobian.weightedVar_eq_sum_sq (beta : ℝ) (s x : Fin m → ℝ) (i : Fin m) :
    weightedVar beta s x
      = ∑ j, scoreSoftmax beta s j * (x j - ∑ l, scoreSoftmax beta s l * x l) ^ 2 := by sorry

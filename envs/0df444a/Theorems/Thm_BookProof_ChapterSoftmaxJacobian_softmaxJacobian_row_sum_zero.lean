-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_softmaxJacobian_row_sum_zero
-- name    : BookProof.ChapterSoftmaxJacobian.softmaxJacobian_row_sum_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:34:39.050883+00:00
-- url     : https://prove2.me/theorems/a84c37ca-8257-443a-83ef-62bf2b1f92c3
-- title:
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_row_sum_zero` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : ∑ j, softmaxJacobian beta s i j = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_row_sum_zero` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : ∑ j, softmaxJacobian beta s i j = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_row_sum_zero`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_row_sum_zero
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

theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_row_sum_zero (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    ∑ j, softmaxJacobian beta s i j = 0 := by sorry

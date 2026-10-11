-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_weightedVar_nonneg
-- name    : BookProof.ChapterSoftmaxJacobian.weightedVar_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:34:05.571343+00:00
-- url     : https://prove2.me/theorems/a364ff02-3716-4ad7-a88d-e29cb7e40428
-- title:
--   `BookProof.ChapterSoftmaxJacobian.weightedVar_nonneg` (beta : ℝ) (s x : Fin m → ℝ) (i : Fin m) : 0 ≤ weightedVar beta s x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.weightedVar_nonneg` (beta : ℝ) (s x : Fin m → ℝ) (i : Fin m) : 0 ≤ weightedVar beta s x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.weightedVar_nonneg`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.weightedVar_nonneg
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

theorem BookProof.ChapterSoftmaxJacobian.weightedVar_nonneg (beta : ℝ) (s x : Fin m → ℝ) (i : Fin m) :
    0 ≤ weightedVar beta s x := by sorry

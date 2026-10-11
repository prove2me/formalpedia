-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_scorePerturb_of_ne
-- name    : BookProof.ChapterSoftmaxJacobian.scorePerturb_of_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:17:56.10498+00:00
-- url     : https://prove2.me/theorems/9c620ec8-0474-4ec8-b0f2-009962e8d39f
-- title:
--   `BookProof.ChapterSoftmaxJacobian.scorePerturb_of_ne` (s : Fin m → ℝ) {i l : Fin m} (h : l ≠ i) (t : ℝ) : scorePerturb s i t l = s l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.scorePerturb_of_ne` (s : Fin m → ℝ) {i l : Fin m} (h : l ≠ i) (t : ℝ) : scorePerturb s i t l = s l
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.scorePerturb_of_ne`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.scorePerturb_of_ne
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
open BookProof.ChapterSoftmaxJacobian


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxJacobian.scorePerturb_of_ne (s : Fin m → ℝ) {i l : Fin m} (h : l ≠ i) (t : ℝ) :
    scorePerturb s i t l = s l := by sorry

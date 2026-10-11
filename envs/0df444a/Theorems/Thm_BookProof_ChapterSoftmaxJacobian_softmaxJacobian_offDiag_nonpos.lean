-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_softmaxJacobian_offDiag_nonpos
-- name    : BookProof.ChapterSoftmaxJacobian.softmaxJacobian_offDiag_nonpos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:33:53.143699+00:00
-- url     : https://prove2.me/theorems/9b7f81c9-3e30-471f-b467-15d15f6f6c2a
-- title:
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_offDiag_nonpos` {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) {i j : Fin m} (hij : j ≠ i) : softmaxJacobian beta s i j ≤ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_offDiag_nonpos` {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) {i j : Fin m} (hij : j ≠ i) : softmaxJacobian beta s i j ≤ 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_offDiag_nonpos`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_offDiag_nonpos
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

theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_offDiag_nonpos {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    {i j : Fin m} (hij : j ≠ i) : softmaxJacobian beta s i j ≤ 0 := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_softmaxJacobian_diag_nonneg
-- name    : BookProof.ChapterSoftmaxJacobian.softmaxJacobian_diag_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:33:44.898289+00:00
-- url     : https://prove2.me/theorems/adfe92d0-9075-4967-8d15-6976d76af93f
-- title:
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_diag_nonneg` {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (i : Fin m) : 0 ≤ softmaxJacobian beta s i i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_diag_nonneg` {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (i : Fin m) : 0 ≤ softmaxJacobian beta s i i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_diag_nonneg`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_diag_nonneg
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

theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_diag_nonneg {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (i : Fin m) :
    0 ≤ softmaxJacobian beta s i i := by sorry

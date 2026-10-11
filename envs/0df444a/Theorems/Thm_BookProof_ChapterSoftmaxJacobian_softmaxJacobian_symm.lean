-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_softmaxJacobian_symm
-- name    : BookProof.ChapterSoftmaxJacobian.softmaxJacobian_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:18:34.446552+00:00
-- url     : https://prove2.me/theorems/842944b4-d9d6-43fe-80dd-f7d739338a1e
-- title:
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_symm` (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) : softmaxJacobian beta s i j = softmaxJacobian beta s j i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_symm` (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) : softmaxJacobian beta s i j = softmaxJacobian beta s j i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_symm`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_symm
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

theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_symm (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) :
    softmaxJacobian beta s i j = softmaxJacobian beta s j i := by sorry

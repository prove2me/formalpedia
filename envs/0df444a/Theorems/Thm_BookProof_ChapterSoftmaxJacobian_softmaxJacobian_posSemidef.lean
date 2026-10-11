-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_softmaxJacobian_posSemidef
-- name    : BookProof.ChapterSoftmaxJacobian.softmaxJacobian_posSemidef
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:34:32.414361+00:00
-- url     : https://prove2.me/theorems/49788cc3-7099-46a2-b5b9-d62ad98f4681
-- title:
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_posSemidef` {beta : ℝ} (hb : 0 ≤ beta) (s x : Fin m → ℝ) (i : Fin m) : 0 ≤ ∑ i, ∑ j, x i * softmaxJacobian beta s i j * x j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_posSemidef` {beta : ℝ} (hb : 0 ≤ beta) (s x : Fin m → ℝ) (i : Fin m) : 0 ≤ ∑ i, ∑ j, x i * softmaxJacobian beta s i j * x j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_posSemidef`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_posSemidef
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
open BookProof.ChapterSoftmaxJacobian


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_posSemidef {beta : ℝ} (hb : 0 ≤ beta) (s x : Fin m → ℝ) (i : Fin m) :
    0 ≤ ∑ i, ∑ j, x i * softmaxJacobian beta s i j * x j := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_softmaxJacobian_quadratic_form
-- name    : BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:34:38.671107+00:00
-- url     : https://prove2.me/theorems/670a6b34-fc81-4620-8b87-86ef53f19e48
-- title:
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form` (beta : ℝ) (s x : Fin m → ℝ) : ∑ i, ∑ j, x i * softmaxJacobian beta s i j * x j = beta * weightedVar beta s x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form` (beta : ℝ) (s x : Fin m → ℝ) : ∑ i, ∑ j, x i * softmaxJacobian beta s i j * x j = beta * weightedVar beta s x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form
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

theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form (beta : ℝ) (s x : Fin m → ℝ) :
    ∑ i, ∑ j, x i * softmaxJacobian beta s i j * x j = beta * weightedVar beta s x := by sorry

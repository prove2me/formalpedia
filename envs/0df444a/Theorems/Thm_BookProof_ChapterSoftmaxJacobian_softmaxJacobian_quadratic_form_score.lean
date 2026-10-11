-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_softmaxJacobian_quadratic_form_score
-- name    : BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form_score
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:35:42.675528+00:00
-- url     : https://prove2.me/theorems/0747ac75-7444-4454-ba1b-8c6e80bca040
-- title:
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form_score` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : ∑ a, ∑ b, s a * softmaxJacobian beta s a b * s b = beta * varScore
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form_score` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : ∑ a, ∑ b, s a * softmaxJacobian beta s a b * s b = beta * varScore beta s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form_score`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form_score
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxJacobian


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form_score (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    ∑ a, ∑ b, s a * softmaxJacobian beta s a b * s b = beta * varScore beta s := by sorry

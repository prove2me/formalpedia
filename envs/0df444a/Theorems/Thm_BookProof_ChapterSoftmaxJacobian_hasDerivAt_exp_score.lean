-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxJacobian_hasDerivAt_exp_score
-- name    : BookProof.ChapterSoftmaxJacobian.hasDerivAt_exp_score
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:18:08.221613+00:00
-- url     : https://prove2.me/theorems/e06cf343-2e58-45f6-8b01-aa09d4896c0f
-- title:
--   `BookProof.ChapterSoftmaxJacobian.hasDerivAt_exp_score` (beta t₀ : ℝ) (c : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (beta * (c + t))) (beta * Real.exp (beta * (c + t₀))) t₀
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxJacobian`.
--
--   `BookProof.ChapterSoftmaxJacobian.hasDerivAt_exp_score` (beta t₀ : ℝ) (c : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (beta * (c + t))) (beta * Real.exp (beta * (c + t₀))) t₀
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxJacobian.hasDerivAt_exp_score`.

-- Generated from ChapterSoftmaxJacobian.lean — theorem BookProof.ChapterSoftmaxJacobian.hasDerivAt_exp_score
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
open BookProof.ChapterSoftmaxJacobian


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxJacobian.hasDerivAt_exp_score (beta t₀ : ℝ) (c : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (beta * (c + t)))
      (beta * Real.exp (beta * (c + t₀))) t₀ := by sorry

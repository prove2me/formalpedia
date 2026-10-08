-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionFactorization_prodSoftmax_sum_one
-- name    : BookProof.ChapterAttentionFactorization.prodSoftmax_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:56:51.222159+00:00
-- url     : https://prove2.me/theorems/eebd619b-a562-4216-b178-25202f3f0c37
-- title:
--   `BookProof.ChapterAttentionFactorization.prodSoftmax_sum_one` (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ) (i₁ : Fin m₁) (i₂ : Fin m₂) : ∑ j : Fin m₁ × Fin m₂,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionFactorization`.
--
--   `BookProof.ChapterAttentionFactorization.prodSoftmax_sum_one` (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ) (i₁ : Fin m₁) (i₂ : Fin m₂) : ∑ j : Fin m₁ × Fin m₂, prodSoftmax beta s₁ s₂ j = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionFactorization.prodSoftmax_sum_one`.

-- Generated from ChapterAttentionFactorization.lean — theorem BookProof.ChapterAttentionFactorization.prodSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionFactorization
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionFactorization


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m₁ m₂ : ℕ}

theorem BookProof.ChapterAttentionFactorization.prodSoftmax_sum_one (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ)
    (i₁ : Fin m₁) (i₂ : Fin m₂) : ∑ j : Fin m₁ × Fin m₂, prodSoftmax beta s₁ s₂ j = 1 := by sorry

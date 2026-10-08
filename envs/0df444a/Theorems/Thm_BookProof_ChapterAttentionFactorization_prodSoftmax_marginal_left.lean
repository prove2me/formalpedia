-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionFactorization_prodSoftmax_marginal_left
-- name    : BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:57:05.171626+00:00
-- url     : https://prove2.me/theorems/4306ae91-c693-489c-92bf-241b1dd29576
-- title:
--   `BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_left` (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ) (i₂ : Fin m₂) (a : Fin m₁) : ∑ b, prodSoftmax beta...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionFactorization`.
--
--   `BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_left` (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ) (i₂ : Fin m₂) (a : Fin m₁) : ∑ b, prodSoftmax beta s₁ s₂ (a, b) = scoreSoftmax beta s₁ a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_left`.

-- Generated from ChapterAttentionFactorization.lean — theorem BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_left
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

theorem BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_left (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ)
    (i₂ : Fin m₂) (a : Fin m₁) :
    ∑ b, prodSoftmax beta s₁ s₂ (a, b) = scoreSoftmax beta s₁ a := by sorry

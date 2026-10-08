-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionFactorization_prodSoftmax_marginal_right
-- name    : BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_right
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:23:31.477223+00:00
-- url     : https://prove2.me/theorems/9871d0c3-d66e-427f-9dce-c7cf85929929
-- title:
--   `BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_right` (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ) (i₁ : Fin m₁) (b : Fin m₂) : ∑ a, prodSoftmax beta...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionFactorization`.
--
--   `BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_right` (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ) (i₁ : Fin m₁) (b : Fin m₂) : ∑ a, prodSoftmax beta s₁ s₂ (a, b) = scoreSoftmax beta s₂ b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_right`.

-- Generated from ChapterAttentionFactorization.lean — theorem BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_right
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

theorem BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_right (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ)
    (i₁ : Fin m₁) (b : Fin m₂) :
    ∑ a, prodSoftmax beta s₁ s₂ (a, b) = scoreSoftmax beta s₂ b := by sorry

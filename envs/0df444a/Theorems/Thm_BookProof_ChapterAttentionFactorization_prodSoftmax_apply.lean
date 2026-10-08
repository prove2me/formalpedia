-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionFactorization_prodSoftmax_apply
-- name    : BookProof.ChapterAttentionFactorization.prodSoftmax_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:57:14.323717+00:00
-- url     : https://prove2.me/theorems/1cf89cfd-4ef6-4bed-b927-22e125de33fc
-- title:
--   `BookProof.ChapterAttentionFactorization.prodSoftmax_apply` (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ) (a : Fin m₁) (b : Fin m₂) : prodSoftmax beta s₁ s₂ (a, b) =...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionFactorization`.
--
--   `BookProof.ChapterAttentionFactorization.prodSoftmax_apply` (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ) (a : Fin m₁) (b : Fin m₂) : prodSoftmax beta s₁ s₂ (a, b) = scoreSoftmax beta s₁ a * scoreSoftmax beta s₂ b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionFactorization.prodSoftmax_apply`.

-- Generated from ChapterAttentionFactorization.lean — theorem BookProof.ChapterAttentionFactorization.prodSoftmax_apply
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

theorem BookProof.ChapterAttentionFactorization.prodSoftmax_apply (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ)
    (a : Fin m₁) (b : Fin m₂) :
    prodSoftmax beta s₁ s₂ (a, b) = scoreSoftmax beta s₁ a * scoreSoftmax beta s₂ b := by sorry

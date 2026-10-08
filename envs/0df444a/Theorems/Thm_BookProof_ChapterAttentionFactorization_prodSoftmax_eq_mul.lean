-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionFactorization_prodSoftmax_eq_mul
-- name    : BookProof.ChapterAttentionFactorization.prodSoftmax_eq_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:57:48.097653+00:00
-- url     : https://prove2.me/theorems/09c52f9f-42d7-4781-9aea-6f1dbfd0366e
-- title:
--   `BookProof.ChapterAttentionFactorization.prodSoftmax_eq_mul` (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ) (j : Fin m₁ × Fin m₂) : prodSoftmax beta s₁ s₂ j =...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionFactorization`.
--
--   `BookProof.ChapterAttentionFactorization.prodSoftmax_eq_mul` (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ) (j : Fin m₁ × Fin m₂) : prodSoftmax beta s₁ s₂ j = scoreSoftmax beta s₁ j.1 * scoreSoftmax beta s₂ j.2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionFactorization.prodSoftmax_eq_mul`.

-- Generated from ChapterAttentionFactorization.lean — theorem BookProof.ChapterAttentionFactorization.prodSoftmax_eq_mul
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

theorem BookProof.ChapterAttentionFactorization.prodSoftmax_eq_mul (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ)
    (j : Fin m₁ × Fin m₂) :
    prodSoftmax beta s₁ s₂ j = scoreSoftmax beta s₁ j.1 * scoreSoftmax beta s₂ j.2 := by sorry

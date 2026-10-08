-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMarkov_attentionMatrix_isStochastic
-- name    : BookProof.ChapterAttentionMarkov.attentionMatrix_isStochastic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:27:14.576643+00:00
-- url     : https://prove2.me/theorems/884a417a-21d7-44d4-b497-b5b133140c4e
-- title:
--   `BookProof.ChapterAttentionMarkov.attentionMatrix_isStochastic` (beta : ℝ) (S : Fin m → Fin m → ℝ) : IsStochastic (attentionMatrix beta S)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMarkov`.
--
--   `BookProof.ChapterAttentionMarkov.attentionMatrix_isStochastic` (beta : ℝ) (S : Fin m → Fin m → ℝ) : IsStochastic (attentionMatrix beta S)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMarkov.attentionMatrix_isStochastic`.

-- Generated from ChapterAttentionMarkov.lean — theorem BookProof.ChapterAttentionMarkov.attentionMatrix_isStochastic
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMarkov.attentionMatrix_isStochastic (beta : ℝ) (S : Fin m → Fin m → ℝ) :
    IsStochastic (attentionMatrix beta S) := by sorry

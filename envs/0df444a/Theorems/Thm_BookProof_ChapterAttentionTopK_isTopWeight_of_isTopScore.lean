-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionTopK_isTopWeight_of_isTopScore
-- name    : BookProof.ChapterAttentionTopK.isTopWeight_of_isTopScore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:51:36.877992+00:00
-- url     : https://prove2.me/theorems/cefe875d-4ba3-44b8-b9d3-4c5eeaced114
-- title:
--   `BookProof.ChapterAttentionTopK.isTopWeight_of_isTopScore` {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : ∀ x ∈ S, ∀ y ∉ S, s y ≤ s x) : IsTop (scoreSoftm
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionTopK`.
--
--   `BookProof.ChapterAttentionTopK.isTopWeight_of_isTopScore` {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : ∀ x ∈ S, ∀ y ∉ S, s y ≤ s x) : IsTop (scoreSoftmax beta s) S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionTopK.isTopWeight_of_isTopScore`.

-- Generated from ChapterAttentionTopK.lean — theorem BookProof.ChapterAttentionTopK.isTopWeight_of_isTopScore
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionTopK
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionTopK


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionTopK.isTopWeight_of_isTopScore {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ)
    {S : Finset (Fin m)} (hS : ∀ x ∈ S, ∀ y ∉ S, s y ≤ s x) :
    IsTop (scoreSoftmax beta s) S := by sorry

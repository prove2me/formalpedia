-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionTopK_sum_le_sum_of_isTop
-- name    : BookProof.ChapterAttentionTopK.sum_le_sum_of_isTop
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:51:54.180569+00:00
-- url     : https://prove2.me/theorems/4f5cefba-8f1c-48ba-908e-02205b6044f9
-- title:
--   `BookProof.ChapterAttentionTopK.sum_le_sum_of_isTop` {p : Fin m → ℝ} (hp : ∀ x, 0 ≤ p x) {S T : Finset (Fin m)} (hS : IsTop p S) (hcard : T.card ≤ S.card) : ∑ x ∈ T, p x ≤ ∑ x ∈ S,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionTopK`.
--
--   `BookProof.ChapterAttentionTopK.sum_le_sum_of_isTop` {p : Fin m → ℝ} (hp : ∀ x, 0 ≤ p x) {S T : Finset (Fin m)} (hS : IsTop p S) (hcard : T.card ≤ S.card) : ∑ x ∈ T, p x ≤ ∑ x ∈ S, p x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionTopK.sum_le_sum_of_isTop`.

-- Generated from ChapterAttentionTopK.lean — theorem BookProof.ChapterAttentionTopK.sum_le_sum_of_isTop
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionTopK
open BookProof.ChapterAttentionTopK


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionTopK.sum_le_sum_of_isTop {p : Fin m → ℝ} (hp : ∀ x, 0 ≤ p x) {S T : Finset (Fin m)}
    (hS : IsTop p S) (hcard : T.card ≤ S.card) :
    ∑ x ∈ T, p x ≤ ∑ x ∈ S, p x := by sorry

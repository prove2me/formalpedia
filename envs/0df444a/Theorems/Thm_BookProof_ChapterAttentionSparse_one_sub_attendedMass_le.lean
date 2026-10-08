-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSparse_one_sub_attendedMass_le
-- name    : BookProof.ChapterAttentionSparse.one_sub_attendedMass_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:49:19.68526+00:00
-- url     : https://prove2.me/theorems/aabdb7d1-1eec-4801-a859-7fd1b3a06b86
-- title:
--   `BookProof.ChapterAttentionSparse.one_sub_attendedMass_le` (beta : ℝ) (s : Fin m → ℝ) (S : Finset (Fin m)) (i : Fin m) {eps : ℝ} (h : ∀ l ∉ S, scoreSoftmax beta s l ≤ eps) : 1 - at
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSparse`.
--
--   `BookProof.ChapterAttentionSparse.one_sub_attendedMass_le` (beta : ℝ) (s : Fin m → ℝ) (S : Finset (Fin m)) (i : Fin m) {eps : ℝ} (h : ∀ l ∉ S, scoreSoftmax beta s l ≤ eps) : 1 - attendedMass beta s S ≤ (m - S.card : ℝ) * eps
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSparse.one_sub_attendedMass_le`.

-- Generated from ChapterAttentionSparse.lean — theorem BookProof.ChapterAttentionSparse.one_sub_attendedMass_le
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionSparse
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSparse


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionSparse.one_sub_attendedMass_le (beta : ℝ) (s : Fin m → ℝ) (S : Finset (Fin m)) (i : Fin m)
    {eps : ℝ} (h : ∀ l ∉ S, scoreSoftmax beta s l ≤ eps) :
    1 - attendedMass beta s S ≤ (m - S.card : ℝ) * eps := by sorry

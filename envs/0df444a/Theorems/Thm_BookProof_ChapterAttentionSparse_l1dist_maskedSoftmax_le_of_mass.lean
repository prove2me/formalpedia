-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSparse_l1dist_maskedSoftmax_le_of_mass
-- name    : BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_le_of_mass
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T09:48:29.668691+00:00
-- url     : https://prove2.me/theorems/a907aba8-a127-4827-9345-24bdc42158d4
-- title:
--   `BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_le_of_mass` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) (i : Fin m) {eps : ℝ} (h : 1 - eps ≤ attendedMa
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSparse`.
--
--   `BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_le_of_mass` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) (i : Fin m) {eps : ℝ} (h : 1 - eps ≤ attendedMass beta s S) : l1dist (maskedSoftmax beta s S) (scoreSoftmax beta s) ≤ 2 * eps
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_le_of_mass`.

-- Generated from ChapterAttentionSparse.lean — theorem BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_le_of_mass
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionSparse
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionMarkov
import Definitions.Def_ChapterAttentionMasking
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSparse


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionMarkov
open BookProof.ChapterAttentionMasking

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_le_of_mass (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    (hS : S.Nonempty) (i : Fin m) {eps : ℝ} (h : 1 - eps ≤ attendedMass beta s S) :
    l1dist (maskedSoftmax beta s S) (scoreSoftmax beta s) ≤ 2 * eps := by sorry

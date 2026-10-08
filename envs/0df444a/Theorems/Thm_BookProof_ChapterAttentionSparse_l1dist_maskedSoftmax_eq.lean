-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSparse_l1dist_maskedSoftmax_eq
-- name    : BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:29:17.557986+00:00
-- url     : https://prove2.me/theorems/83362aed-db55-4516-86f4-a6f2b9aceece
-- title:
--   `BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) (i : Fin m) : l1dist (maskedSoftmax beta s S) (scoreSof
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSparse`.
--
--   `BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) (i : Fin m) : l1dist (maskedSoftmax beta s S) (scoreSoftmax beta s) = 2 * (1 - attendedMass beta s S)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq`.

-- Generated from ChapterAttentionSparse.lean — theorem BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq
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

theorem BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    (hS : S.Nonempty) (i : Fin m) :
    l1dist (maskedSoftmax beta s S) (scoreSoftmax beta s)
      = 2 * (1 - attendedMass beta s S) := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSparse_l1dist_maskedSoftmax_eq_zero_iff_mass_one
-- name    : BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq_zero_iff_mass_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T09:51:09.243034+00:00
-- url     : https://prove2.me/theorems/a5c53a79-6a7d-46f5-94d6-8f297aea1760
-- title:
--   `BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq_zero_iff_mass_one` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) (i : Fin m) : l1dist (maskedSoftmax b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSparse`.
--
--   `BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq_zero_iff_mass_one` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) (i : Fin m) : l1dist (maskedSoftmax beta s S) (scoreSoftmax beta s) = 0 ↔ attendedMass beta s S = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq_zero_iff_mass_one`.

-- Generated from ChapterAttentionSparse.lean — theorem BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq_zero_iff_mass_one
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

theorem BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq_zero_iff_mass_one (beta : ℝ) (s : Fin m → ℝ)
    {S : Finset (Fin m)} (hS : S.Nonempty) (i : Fin m) :
    l1dist (maskedSoftmax beta s S) (scoreSoftmax beta s) = 0
      ↔ attendedMass beta s S = 1 := by sorry

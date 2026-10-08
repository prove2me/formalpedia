-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSparse_maskedSoftmax_eq_of_mass_one
-- name    : BookProof.ChapterAttentionSparse.maskedSoftmax_eq_of_mass_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:49:28.514138+00:00
-- url     : https://prove2.me/theorems/13b1d647-4467-4746-97af-8c5e70fd5c16
-- title:
--   `BookProof.ChapterAttentionSparse.maskedSoftmax_eq_of_mass_one` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) (i : Fin m) (h : attendedMass beta s S = 1) (j : F
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSparse`.
--
--   `BookProof.ChapterAttentionSparse.maskedSoftmax_eq_of_mass_one` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) (i : Fin m) (h : attendedMass beta s S = 1) (j : Fin m) : maskedSoftmax beta s S j = scoreSoftmax beta s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSparse.maskedSoftmax_eq_of_mass_one`.

-- Generated from ChapterAttentionSparse.lean — theorem BookProof.ChapterAttentionSparse.maskedSoftmax_eq_of_mass_one
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionSparse
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionMasking
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSparse


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionMasking

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionSparse.maskedSoftmax_eq_of_mass_one (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    (hS : S.Nonempty) (i : Fin m) (h : attendedMass beta s S = 1) (j : Fin m) :
    maskedSoftmax beta s S j = scoreSoftmax beta s j := by sorry

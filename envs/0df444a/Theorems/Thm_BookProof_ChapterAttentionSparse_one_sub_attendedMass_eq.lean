-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSparse_one_sub_attendedMass_eq
-- name    : BookProof.ChapterAttentionSparse.one_sub_attendedMass_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:49:18.26341+00:00
-- url     : https://prove2.me/theorems/b696bd4c-97ff-4c0e-943b-70e8037f599b
-- title:
--   `BookProof.ChapterAttentionSparse.one_sub_attendedMass_eq` (beta : ℝ) (s : Fin m → ℝ) (S : Finset (Fin m)) (i : Fin m) : 1 - attendedMass beta s S = ∑ l ∈ Sᶜ, scoreSoftmax beta s l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSparse`.
--
--   `BookProof.ChapterAttentionSparse.one_sub_attendedMass_eq` (beta : ℝ) (s : Fin m → ℝ) (S : Finset (Fin m)) (i : Fin m) : 1 - attendedMass beta s S = ∑ l ∈ Sᶜ, scoreSoftmax beta s l
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSparse.one_sub_attendedMass_eq`.

-- Generated from ChapterAttentionSparse.lean — theorem BookProof.ChapterAttentionSparse.one_sub_attendedMass_eq
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

theorem BookProof.ChapterAttentionSparse.one_sub_attendedMass_eq (beta : ℝ) (s : Fin m → ℝ) (S : Finset (Fin m)) (i : Fin m) :
    1 - attendedMass beta s S = ∑ l ∈ Sᶜ, scoreSoftmax beta s l := by sorry

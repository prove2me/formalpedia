-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionTopK_attendedMass_le_of_isTop
-- name    : BookProof.ChapterAttentionTopK.attendedMass_le_of_isTop
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:51:45.886012+00:00
-- url     : https://prove2.me/theorems/dd8db806-9d2f-442b-b23b-44f375125888
-- title:
--   `BookProof.ChapterAttentionTopK.attendedMass_le_of_isTop` (beta : ℝ) (s : Fin m → ℝ) {S T : Finset (Fin m)} (hS : IsTop (scoreSoftmax beta s) S) (hcard : T.card ≤ S.card) : attende
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionTopK`.
--
--   `BookProof.ChapterAttentionTopK.attendedMass_le_of_isTop` (beta : ℝ) (s : Fin m → ℝ) {S T : Finset (Fin m)} (hS : IsTop (scoreSoftmax beta s) S) (hcard : T.card ≤ S.card) : attendedMass beta s T ≤ attendedMass beta s S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionTopK.attendedMass_le_of_isTop`.

-- Generated from ChapterAttentionTopK.lean — theorem BookProof.ChapterAttentionTopK.attendedMass_le_of_isTop
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionTopK
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionSparse
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionTopK


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionSparse

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionTopK.attendedMass_le_of_isTop (beta : ℝ) (s : Fin m → ℝ) {S T : Finset (Fin m)}
    (hS : IsTop (scoreSoftmax beta s) S) (hcard : T.card ≤ S.card) :
    attendedMass beta s T ≤ attendedMass beta s S := by sorry

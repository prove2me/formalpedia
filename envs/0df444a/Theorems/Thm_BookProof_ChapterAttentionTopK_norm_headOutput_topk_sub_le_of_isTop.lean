-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionTopK_norm_headOutput_topk_sub_le_of_isTop
-- name    : BookProof.ChapterAttentionTopK.norm_headOutput_topk_sub_le_of_isTop
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:52:00.575496+00:00
-- url     : https://prove2.me/theorems/45d7ba5f-0a3c-4496-acfc-cf3bef69f4ba
-- title:
--   `BookProof.ChapterAttentionTopK.norm_headOutput_topk_sub_le_of_isTop` (beta : ℝ) (s : Fin m → ℝ) {S T : Finset (Fin m)} (hS : IsTop (scoreSoftmax beta s) S) (hcard : T.card ≤ S.car
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionTopK`.
--
--   `BookProof.ChapterAttentionTopK.norm_headOutput_topk_sub_le_of_isTop` (beta : ℝ) (s : Fin m → ℝ) {S T : Finset (Fin m)} (hS : IsTop (scoreSoftmax beta s) S) (hcard : T.card ≤ S.card) (hSne : S.Nonempty) (i : Fin m) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) (hC : 0 ≤ C) : ‖observableExpectation (maskedSoftmax beta s S) v - headOutput beta s v‖ ≤ 2 * (1 - attendedMass beta s T) * C
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionTopK.norm_headOutput_topk_sub_le_of_isTop`.

-- Generated from ChapterAttentionTopK.lean — theorem BookProof.ChapterAttentionTopK.norm_headOutput_topk_sub_le_of_isTop
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionTopK
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionMasking
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterAttentionTopK
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterAttentionSparse
open BookProof.ChapterObservableExpectation
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionTopK


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionMasking
open BookProof.ChapterAttentionOutput
open BookProof.ChapterAttentionSparse

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionTopK.norm_headOutput_topk_sub_le_of_isTop (beta : ℝ) (s : Fin m → ℝ)
    {S T : Finset (Fin m)} (hS : IsTop (scoreSoftmax beta s) S) (hcard : T.card ≤ S.card)
    (hSne : S.Nonempty) (i : Fin m) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C)
    (hC : 0 ≤ C) :
    ‖observableExpectation (maskedSoftmax beta s S) v - headOutput beta s v‖
      ≤ 2 * (1 - attendedMass beta s T) * C := by sorry

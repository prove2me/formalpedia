-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSparse_norm_headOutput_masked_sub_le
-- name    : BookProof.ChapterAttentionSparse.norm_headOutput_masked_sub_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T09:49:13.268119+00:00
-- url     : https://prove2.me/theorems/f297b8ff-ff8f-43e2-bfdf-d00e16013b79
-- title:
--   `BookProof.ChapterAttentionSparse.norm_headOutput_masked_sub_le` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) (i : Fin m) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSparse`.
--
--   `BookProof.ChapterAttentionSparse.norm_headOutput_masked_sub_le` (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) (i : Fin m) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) : ‖observableExpectation (maskedSoftmax beta s S) v - headOutput beta s v‖ ≤ 2 * (1 - attendedMass beta s S) * C
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSparse.norm_headOutput_masked_sub_le`.

-- Generated from ChapterAttentionSparse.lean — theorem BookProof.ChapterAttentionSparse.norm_headOutput_masked_sub_le
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionSparse
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionMasking
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterObservableExpectation
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSparse


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionMasking
open BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionSparse.norm_headOutput_masked_sub_le (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    (hS : S.Nonempty) (i : Fin m) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) :
    ‖observableExpectation (maskedSoftmax beta s S) v - headOutput beta s v‖
      ≤ 2 * (1 - attendedMass beta s S) * C := by sorry

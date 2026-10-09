-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutput_norm_observableExpectation_sub_le
-- name    : BookProof.ChapterAttentionOutput.norm_observableExpectation_sub_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:34:06.711131+00:00
-- url     : https://prove2.me/theorems/ac59f968-9c05-4916-a2cd-763584c2e383
-- title:
--   `BookProof.ChapterAttentionOutput.norm_observableExpectation_sub_le` (p q : Fin m → ℝ) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) : ‖observableExpectation p v - observableExpect
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutput`.
--
--   `BookProof.ChapterAttentionOutput.norm_observableExpectation_sub_le` (p q : Fin m → ℝ) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) : ‖observableExpectation p v - observableExpectation q v‖ ≤ (∑ j, |p j - q j|) * C
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutput.norm_observableExpectation_sub_le`.

-- Generated from ChapterAttentionOutput.lean — theorem BookProof.ChapterAttentionOutput.norm_observableExpectation_sub_le
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation
open BookProof.ChapterAttentionOutput


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionOutput.norm_observableExpectation_sub_le (p q : Fin m → ℝ) {v : Fin m → E} {C : ℝ}
    (hv : ∀ j, ‖v j‖ ≤ C) :
    ‖observableExpectation p v - observableExpectation q v‖ ≤ (∑ j, |p j - q j|) * C := by sorry

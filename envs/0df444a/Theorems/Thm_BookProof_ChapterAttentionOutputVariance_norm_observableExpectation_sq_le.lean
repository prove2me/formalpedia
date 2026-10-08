-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutputVariance_norm_observableExpectation_sq_le
-- name    : BookProof.ChapterAttentionOutputVariance.norm_observableExpectation_sq_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:38:10.474989+00:00
-- url     : https://prove2.me/theorems/46f4f3ef-a25c-45ec-990f-30e0e82cc6dc
-- title:
--   `BookProof.ChapterAttentionOutputVariance.norm_observableExpectation_sq_le` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = 1) (v : Fin m → E) : ‖observableExpectation p v‖ ^
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutputVariance`.
--
--   `BookProof.ChapterAttentionOutputVariance.norm_observableExpectation_sq_le` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = 1) (v : Fin m → E) : ‖observableExpectation p v‖ ^ 2 ≤ ∑ j, p j * ‖v j‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutputVariance.norm_observableExpectation_sq_le`.

-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.norm_observableExpectation_sq_le
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation
open BookProof.ChapterAttentionOutputVariance


open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterAttentionOutputVariance.norm_observableExpectation_sq_le {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hp : ∑ j, p j = 1) (v : Fin m → E) :
    ‖observableExpectation p v‖ ^ 2 ≤ ∑ j, p j * ‖v j‖ ^ 2 := by sorry

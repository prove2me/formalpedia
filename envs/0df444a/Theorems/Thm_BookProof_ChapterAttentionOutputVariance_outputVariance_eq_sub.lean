-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutputVariance_outputVariance_eq_sub
-- name    : BookProof.ChapterAttentionOutputVariance.outputVariance_eq_sub
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:37:44.705104+00:00
-- url     : https://prove2.me/theorems/b8120493-253b-438a-8fcc-14635817654f
-- title:
--   `BookProof.ChapterAttentionOutputVariance.outputVariance_eq_sub` {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E) : outputVariance p v = (∑ j, p j * ‖v j‖ ^ 2) - ‖observableExpe
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutputVariance`.
--
--   `BookProof.ChapterAttentionOutputVariance.outputVariance_eq_sub` {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E) : outputVariance p v = (∑ j, p j * ‖v j‖ ^ 2) - ‖observableExpectation p v‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutputVariance.outputVariance_eq_sub`.

-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.outputVariance_eq_sub
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

theorem BookProof.ChapterAttentionOutputVariance.outputVariance_eq_sub {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E) :
    outputVariance p v = (∑ j, p j * ‖v j‖ ^ 2) - ‖observableExpectation p v‖ ^ 2 := by sorry

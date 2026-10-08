-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutputVariance_outputVariance_eq_zero_iff_of_pos
-- name    : BookProof.ChapterAttentionOutputVariance.outputVariance_eq_zero_iff_of_pos
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:38:12.877893+00:00
-- url     : https://prove2.me/theorems/872ef2bb-0ea3-4c0f-98a5-75b05eb2fffe
-- title:
--   `BookProof.ChapterAttentionOutputVariance.outputVariance_eq_zero_iff_of_pos` {p : Fin m → ℝ} (hp0 : ∀ j, 0 < p j) (v : Fin m → E) : outputVariance p v = 0 ↔ ∀ j, v j = observableEx
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutputVariance`.
--
--   `BookProof.ChapterAttentionOutputVariance.outputVariance_eq_zero_iff_of_pos` {p : Fin m → ℝ} (hp0 : ∀ j, 0 < p j) (v : Fin m → E) : outputVariance p v = 0 ↔ ∀ j, v j = observableExpectation p v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutputVariance.outputVariance_eq_zero_iff_of_pos`.

-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.outputVariance_eq_zero_iff_of_pos
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

theorem BookProof.ChapterAttentionOutputVariance.outputVariance_eq_zero_iff_of_pos {p : Fin m → ℝ} (hp0 : ∀ j, 0 < p j)
    (v : Fin m → E) :
    outputVariance p v = 0 ↔ ∀ j, v j = observableExpectation p v := by sorry

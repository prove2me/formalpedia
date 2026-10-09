-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutputVariance_observableExpectation_minimizes
-- name    : BookProof.ChapterAttentionOutputVariance.observableExpectation_minimizes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:37:40.509991+00:00
-- url     : https://prove2.me/theorems/71a219b9-c529-4c96-b34a-7da5b64cc103
-- title:
--   `BookProof.ChapterAttentionOutputVariance.observableExpectation_minimizes` {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E) (c : E) : ∑ j, p j * ‖v j - observableExpectation p v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutputVariance`.
--
--   `BookProof.ChapterAttentionOutputVariance.observableExpectation_minimizes` {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E) (c : E) : ∑ j, p j * ‖v j - observableExpectation p v‖ ^ 2 ≤ ∑ j, p j * ‖v j - c‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutputVariance.observableExpectation_minimizes`.

-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.observableExpectation_minimizes
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

theorem BookProof.ChapterAttentionOutputVariance.observableExpectation_minimizes {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E)
    (c : E) :
    ∑ j, p j * ‖v j - observableExpectation p v‖ ^ 2 ≤ ∑ j, p j * ‖v j - c‖ ^ 2 := by sorry

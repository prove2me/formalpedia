-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutputVariance_sum_dist_sq_eq
-- name    : BookProof.ChapterAttentionOutputVariance.sum_dist_sq_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:35:16.000842+00:00
-- url     : https://prove2.me/theorems/1774489c-eba2-48d9-81bd-7fd194c5bed9
-- title:
--   `BookProof.ChapterAttentionOutputVariance.sum_dist_sq_eq` {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E) (c : E) : ∑ j, p j * ‖v j - c‖ ^ 2 = outputVariance p v + ‖observableE
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutputVariance`.
--
--   `BookProof.ChapterAttentionOutputVariance.sum_dist_sq_eq` {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E) (c : E) : ∑ j, p j * ‖v j - c‖ ^ 2 = outputVariance p v + ‖observableExpectation p v - c‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutputVariance.sum_dist_sq_eq`.

-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.sum_dist_sq_eq
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

theorem BookProof.ChapterAttentionOutputVariance.sum_dist_sq_eq {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E) (c : E) :
    ∑ j, p j * ‖v j - c‖ ^ 2
      = outputVariance p v + ‖observableExpectation p v - c‖ ^ 2 := by sorry

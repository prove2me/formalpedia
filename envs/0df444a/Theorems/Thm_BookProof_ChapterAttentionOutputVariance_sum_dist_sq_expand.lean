-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutputVariance_sum_dist_sq_expand
-- name    : BookProof.ChapterAttentionOutputVariance.sum_dist_sq_expand
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:34:38.156701+00:00
-- url     : https://prove2.me/theorems/a1dc63e4-5410-4652-a757-57ec4f43ec2e
-- title:
--   `BookProof.ChapterAttentionOutputVariance.sum_dist_sq_expand` {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E) (c : E) : ∑ j, p j * ‖v j - c‖ ^ 2 = (∑ j, p j * ‖v j‖ ^ 2) - 2 *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutputVariance`.
--
--   `BookProof.ChapterAttentionOutputVariance.sum_dist_sq_expand` {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E) (c : E) : ∑ j, p j * ‖v j - c‖ ^ 2 = (∑ j, p j * ‖v j‖ ^ 2) - 2 * ⟪observableExpectation p v, c⟫ + ‖c‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutputVariance.sum_dist_sq_expand`.

-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.sum_dist_sq_expand
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

theorem BookProof.ChapterAttentionOutputVariance.sum_dist_sq_expand {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E) (c : E) :
    ∑ j, p j * ‖v j - c‖ ^ 2
      = (∑ j, p j * ‖v j‖ ^ 2) - 2 * ⟪observableExpectation p v, c⟫ + ‖c‖ ^ 2 := by sorry

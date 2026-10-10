-- Prove2me | Theorems.Thm_BookProof_ChapterObservableExpectation_prob_weighted_sum_mem_convexHull
-- name    : BookProof.ChapterObservableExpectation.prob_weighted_sum_mem_convexHull
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:39:11.015953+00:00
-- url     : https://prove2.me/theorems/11a2c7d9-170b-4863-89b3-77e548f97dc6
-- title:
--   `BookProof.ChapterObservableExpectation.prob_weighted_sum_mem_convexHull` (p : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (v : Fin m → E) : observableExpectation p v ∈ con
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableExpectation`.
--
--   `BookProof.ChapterObservableExpectation.prob_weighted_sum_mem_convexHull` (p : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (v : Fin m → E) : observableExpectation p v ∈ convexHull ℝ (Set.range v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableExpectation.prob_weighted_sum_mem_convexHull`.

-- Generated from ChapterObservableExpectation.lean — theorem BookProof.ChapterObservableExpectation.prob_weighted_sum_mem_convexHull
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem BookProof.ChapterObservableExpectation.prob_weighted_sum_mem_convexHull (p : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hp1 : ∑ j, p j = 1) (v : Fin m → E) :
    observableExpectation p v ∈ convexHull ℝ (Set.range v) := by sorry

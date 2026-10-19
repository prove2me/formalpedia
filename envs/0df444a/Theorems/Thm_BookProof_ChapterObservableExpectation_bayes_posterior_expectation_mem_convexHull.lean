-- Prove2me | Theorems.Thm_BookProof_ChapterObservableExpectation_bayes_posterior_expectation_mem_convexHull
-- name    : BookProof.ChapterObservableExpectation.bayes_posterior_expectation_mem_convexHull
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:43:38.776873+00:00
-- url     : https://prove2.me/theorems/521fd24c-3aca-4486-a3a4-a301353c0399
-- title:
--   `BookProof.ChapterObservableExpectation.bayes_posterior_expectation_mem_convexHull` (prior : Fin m → ℝ) (L : Fin m → Y → ℝ) (y : Y) (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableExpectation`.
--
--   `BookProof.ChapterObservableExpectation.bayes_posterior_expectation_mem_convexHull` (prior : Fin m → ℝ) (L : Fin m → Y → ℝ) (y : Y) (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y) (hy : 0 < evidence prior L y) (v : Fin m → E) : observableExpectation (posterior prior L y) v ∈ convexHull ℝ (Set.range v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableExpectation.bayes_posterior_expectation_mem_convexHull`.

-- Generated from ChapterObservableExpectation.lean — theorem BookProof.ChapterObservableExpectation.bayes_posterior_expectation_mem_convexHull
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterObservableExpectation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

variable {Y : Type*}

theorem BookProof.ChapterObservableExpectation.bayes_posterior_expectation_mem_convexHull
    (prior : Fin m → ℝ) (L : Fin m → Y → ℝ) (y : Y)
    (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y)
    (hy : 0 < evidence prior L y) (v : Fin m → E) :
    observableExpectation (posterior prior L y) v ∈ convexHull ℝ (Set.range v) := by sorry

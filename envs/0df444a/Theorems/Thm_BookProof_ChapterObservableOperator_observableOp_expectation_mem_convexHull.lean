-- Prove2me | Theorems.Thm_BookProof_ChapterObservableOperator_observableOp_expectation_mem_convexHull
-- name    : BookProof.ChapterObservableOperator.observableOp_expectation_mem_convexHull
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:43:36.158901+00:00
-- url     : https://prove2.me/theorems/2302528e-9c48-4704-abb8-883d18911f8d
-- title:
--   `BookProof.ChapterObservableOperator.observableOp_expectation_mem_convexHull` (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin m → ℝ) (q : EuclideanSpace ℂ (Fin
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableOperator`.
--
--   `BookProof.ChapterObservableOperator.observableOp_expectation_mem_convexHull` (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin m → ℝ) (q : EuclideanSpace ℂ (Fin n)) (hq : ‖q‖ = 1) : BookProof.ChapterObservableExpectation.observableExpectation (bornProb (fun j => b j) q) v ∈ convexHull ℝ (Set.range v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableOperator.observableOp_expectation_mem_convexHull`.

-- Generated from ChapterObservableOperator.lean — theorem BookProof.ChapterObservableOperator.observableOp_expectation_mem_convexHull
import Mathlib
import Definitions.Def_ChapterObservableOperator
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterDoubleSlit
open BookProof.ChapterObservableExpectation
open BookProof.ChapterObservableOperator


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterObservableOperator.observableOp_expectation_mem_convexHull
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin m → ℝ)
    (q : EuclideanSpace ℂ (Fin n)) (hq : ‖q‖ = 1) :
    BookProof.ChapterObservableExpectation.observableExpectation
        (bornProb (fun j => b j) q) v ∈ convexHull ℝ (Set.range v) := by sorry

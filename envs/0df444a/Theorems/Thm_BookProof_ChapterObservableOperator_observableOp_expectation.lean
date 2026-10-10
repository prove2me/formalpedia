-- Prove2me | Theorems.Thm_BookProof_ChapterObservableOperator_observableOp_expectation
-- name    : BookProof.ChapterObservableOperator.observableOp_expectation
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:40:17.345599+00:00
-- url     : https://prove2.me/theorems/a5fc74a3-8b90-484f-b995-d69aa24f040e
-- title:
--   `BookProof.ChapterObservableOperator.observableOp_expectation` (k : Fin m → EuclideanSpace ℂ (Fin n)) (v : Fin m → ℝ) (q : EuclideanSpace ℂ (Fin n)) : expectation (observableOp k v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableOperator`.
--
--   `BookProof.ChapterObservableOperator.observableOp_expectation` (k : Fin m → EuclideanSpace ℂ (Fin n)) (v : Fin m → ℝ) (q : EuclideanSpace ℂ (Fin n)) : expectation (observableOp k v) q = ((BookProof.ChapterObservableExpectation.observableExpectation (bornProb k q) v : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableOperator.observableOp_expectation`.

-- Generated from ChapterObservableOperator.lean — theorem BookProof.ChapterObservableOperator.observableOp_expectation
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

theorem BookProof.ChapterObservableOperator.observableOp_expectation (k : Fin m → EuclideanSpace ℂ (Fin n)) (v : Fin m → ℝ)
    (q : EuclideanSpace ℂ (Fin n)) :
    expectation (observableOp k v) q
      = ((BookProof.ChapterObservableExpectation.observableExpectation
            (bornProb k q) v : ℝ) : ℂ) := by sorry

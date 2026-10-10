-- Prove2me | Theorems.Thm_BookProof_ChapterObservableOperator_observable_expectation_born
-- name    : BookProof.ChapterObservableOperator.observable_expectation_born
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:40:44.706259+00:00
-- url     : https://prove2.me/theorems/88bd8fb8-92ac-4058-a1ad-0a0e9f21713d
-- title:
--   `BookProof.ChapterObservableOperator.observable_expectation_born` (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin m → ℝ) (q : EuclideanSpace ℂ (Fin n)) (hq : ‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableOperator`.
--
--   `BookProof.ChapterObservableOperator.observable_expectation_born` (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin m → ℝ) (q : EuclideanSpace ℂ (Fin n)) (hq : ‖q‖ = 1) : (∀ j, 0 ≤ bornProb (fun j => b j) q j) ∧ (∑ j, bornProb (fun j => b j) q j = 1) ∧ expectation (observableOp (fun j => b j) v) q = ((∑ j, bornProb (fun j => b j) q j * v j : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableOperator.observable_expectation_born`.

-- Generated from ChapterObservableOperator.lean — theorem BookProof.ChapterObservableOperator.observable_expectation_born
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

theorem BookProof.ChapterObservableOperator.observable_expectation_born (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin n)))
    (v : Fin m → ℝ) (q : EuclideanSpace ℂ (Fin n)) (hq : ‖q‖ = 1) :
    (∀ j, 0 ≤ bornProb (fun j => b j) q j) ∧
      (∑ j, bornProb (fun j => b j) q j = 1) ∧
      expectation (observableOp (fun j => b j) v) q
        = ((∑ j, bornProb (fun j => b j) q j * v j : ℝ) : ℂ) := by sorry

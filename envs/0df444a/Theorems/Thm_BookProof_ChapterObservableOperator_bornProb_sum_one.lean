-- Prove2me | Theorems.Thm_BookProof_ChapterObservableOperator_bornProb_sum_one
-- name    : BookProof.ChapterObservableOperator.bornProb_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:40:40.162977+00:00
-- url     : https://prove2.me/theorems/ec53f5fe-e846-42c5-8b9c-2fcec20e91d3
-- title:
--   `BookProof.ChapterObservableOperator.bornProb_sum_one` (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin n))) (q : EuclideanSpace ℂ (Fin n)) (hq : ‖q‖ = 1) : ∑ j, bornProb (fu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableOperator`.
--
--   `BookProof.ChapterObservableOperator.bornProb_sum_one` (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin n))) (q : EuclideanSpace ℂ (Fin n)) (hq : ‖q‖ = 1) : ∑ j, bornProb (fun j => b j) q j = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableOperator.bornProb_sum_one`.

-- Generated from ChapterObservableOperator.lean — theorem BookProof.ChapterObservableOperator.bornProb_sum_one
import Mathlib
import Definitions.Def_ChapterObservableOperator
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterObservableOperator


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterObservableOperator.bornProb_sum_one (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin n)))
    (q : EuclideanSpace ℂ (Fin n)) (hq : ‖q‖ = 1) :
    ∑ j, bornProb (fun j => b j) q j = 1 := by sorry

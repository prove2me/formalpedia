-- Prove2me | Theorems.Thm_BookProof_ChapterObservableOperator_bornProb_nonneg
-- name    : BookProof.ChapterObservableOperator.bornProb_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:39:43.810985+00:00
-- url     : https://prove2.me/theorems/1dda9f7b-438f-493b-a42e-ad76f6c86b61
-- title:
--   `BookProof.ChapterObservableOperator.bornProb_nonneg` (k : Fin m → EuclideanSpace ℂ (Fin n)) (q : EuclideanSpace ℂ (Fin n)) (j : Fin m) : 0 ≤ bornProb k q j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableOperator`.
--
--   `BookProof.ChapterObservableOperator.bornProb_nonneg` (k : Fin m → EuclideanSpace ℂ (Fin n)) (q : EuclideanSpace ℂ (Fin n)) (j : Fin m) : 0 ≤ bornProb k q j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableOperator.bornProb_nonneg`.

-- Generated from ChapterObservableOperator.lean — theorem BookProof.ChapterObservableOperator.bornProb_nonneg
import Mathlib
import Definitions.Def_ChapterObservableOperator
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterObservableOperator


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterObservableOperator.bornProb_nonneg (k : Fin m → EuclideanSpace ℂ (Fin n))
    (q : EuclideanSpace ℂ (Fin n)) (j : Fin m) : 0 ≤ bornProb k q j := by sorry

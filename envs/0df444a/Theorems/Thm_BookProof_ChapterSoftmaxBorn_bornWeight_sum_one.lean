-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxBorn_bornWeight_sum_one
-- name    : BookProof.ChapterSoftmaxBorn.bornWeight_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:27:48.120996+00:00
-- url     : https://prove2.me/theorems/a6144c1d-31ce-4e2e-84c4-10e8179aa5d1
-- title:
--   `BookProof.ChapterSoftmaxBorn.bornWeight_sum_one` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j₀ : Fin m) : ∑ j, bornWeight q k j = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxBorn`.
--
--   `BookProof.ChapterSoftmaxBorn.bornWeight_sum_one` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j₀ : Fin m) : ∑ j, bornWeight q k j = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxBorn.bornWeight_sum_one`.

-- Generated from ChapterSoftmaxBorn.lean — theorem BookProof.ChapterSoftmaxBorn.bornWeight_sum_one
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxBorn.bornWeight_sum_one (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j₀ : Fin m) :
    ∑ j, bornWeight q k j = 1 := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxBorn_bornWeight_nonneg
-- name    : BookProof.ChapterSoftmaxBorn.bornWeight_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:28:27.006411+00:00
-- url     : https://prove2.me/theorems/277f2d17-6ca9-47bf-a116-798ab79f6122
-- title:
--   `BookProof.ChapterSoftmaxBorn.bornWeight_nonneg` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 ≤ bornWeight q k j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxBorn`.
--
--   `BookProof.ChapterSoftmaxBorn.bornWeight_nonneg` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 ≤ bornWeight q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxBorn.bornWeight_nonneg`.

-- Generated from ChapterSoftmaxBorn.lean — theorem BookProof.ChapterSoftmaxBorn.bornWeight_nonneg
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxBorn.bornWeight_nonneg (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n))
    (j : Fin m) : 0 ≤ bornWeight q k j := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxBorn_bornWeight_pos
-- name    : BookProof.ChapterSoftmaxBorn.bornWeight_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:08:44.91306+00:00
-- url     : https://prove2.me/theorems/acc66354-d3b9-485b-ade3-d4f2f769d4f0
-- title:
--   `BookProof.ChapterSoftmaxBorn.bornWeight_pos` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 < bornWeight q k j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxBorn`.
--
--   `BookProof.ChapterSoftmaxBorn.bornWeight_pos` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 < bornWeight q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxBorn.bornWeight_pos`.

-- Generated from ChapterSoftmaxBorn.lean — theorem BookProof.ChapterSoftmaxBorn.bornWeight_pos
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxBorn.bornWeight_pos (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n))
    (j : Fin m) : 0 < bornWeight q k j := by sorry

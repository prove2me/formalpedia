-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxBorn_softmax_pos
-- name    : BookProof.ChapterSoftmaxBorn.softmax_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:09:22.53505+00:00
-- url     : https://prove2.me/theorems/51145eb3-b67e-45a7-bc27-42915df5cde5
-- title:
--   `BookProof.ChapterSoftmaxBorn.softmax_pos` (beta : ℝ) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 < softmax beta q k j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxBorn`.
--
--   `BookProof.ChapterSoftmaxBorn.softmax_pos` (beta : ℝ) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 < softmax beta q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxBorn.softmax_pos`.

-- Generated from ChapterSoftmaxBorn.lean — theorem BookProof.ChapterSoftmaxBorn.softmax_pos
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxBorn.softmax_pos (beta : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 < softmax beta q k j := by sorry

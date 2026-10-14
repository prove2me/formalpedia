-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxBorn_softmax_nonneg
-- name    : BookProof.ChapterSoftmaxBorn.softmax_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:09:28.20674+00:00
-- url     : https://prove2.me/theorems/94be4f72-6a82-4c11-9dc9-68c8a1f32f72
-- title:
--   `BookProof.ChapterSoftmaxBorn.softmax_nonneg` (beta : ℝ) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 ≤ softmax beta q k j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxBorn`.
--
--   `BookProof.ChapterSoftmaxBorn.softmax_nonneg` (beta : ℝ) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 ≤ softmax beta q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxBorn.softmax_nonneg`.

-- Generated from ChapterSoftmaxBorn.lean — theorem BookProof.ChapterSoftmaxBorn.softmax_nonneg
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxBorn.softmax_nonneg (beta : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 ≤ softmax beta q k j := by sorry

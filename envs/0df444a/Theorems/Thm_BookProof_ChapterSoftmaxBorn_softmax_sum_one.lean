-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxBorn_softmax_sum_one
-- name    : BookProof.ChapterSoftmaxBorn.softmax_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:09:33.465437+00:00
-- url     : https://prove2.me/theorems/934fcfe9-003c-448d-8168-def695802418
-- title:
--   `BookProof.ChapterSoftmaxBorn.softmax_sum_one` (beta : ℝ) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j₀ : Fin m) : ∑ j, softmax beta q k j = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxBorn`.
--
--   `BookProof.ChapterSoftmaxBorn.softmax_sum_one` (beta : ℝ) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j₀ : Fin m) : ∑ j, softmax beta q k j = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxBorn.softmax_sum_one`.

-- Generated from ChapterSoftmaxBorn.lean — theorem BookProof.ChapterSoftmaxBorn.softmax_sum_one
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxBorn.softmax_sum_one (beta : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j₀ : Fin m) :
    ∑ j, softmax beta q k j = 1 := by sorry

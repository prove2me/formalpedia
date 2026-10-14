-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxBorn_coherentBorn_cancel_q
-- name    : BookProof.ChapterSoftmaxBorn.coherentBorn_cancel_q
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:09:27.545206+00:00
-- url     : https://prove2.me/theorems/e76e4a4e-2141-47b8-90db-d06f8ab85ff6
-- title:
--   `BookProof.ChapterSoftmaxBorn.coherentBorn_cancel_q` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : bornWeight q k j = Real.exp (-‖k j‖ ^ 2) *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxBorn`.
--
--   `BookProof.ChapterSoftmaxBorn.coherentBorn_cancel_q` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : bornWeight q k j = Real.exp (-‖k j‖ ^ 2) * Real.exp (2 * inner ℝ q (k j)) / ∑ l, Real.exp (-‖k l‖ ^ 2) * Real.exp (2 * inner ℝ q (k l))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxBorn.coherentBorn_cancel_q`.

-- Generated from ChapterSoftmaxBorn.lean — theorem BookProof.ChapterSoftmaxBorn.coherentBorn_cancel_q
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxBorn.coherentBorn_cancel_q (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    bornWeight q k j =
      Real.exp (-‖k j‖ ^ 2) * Real.exp (2 * inner ℝ q (k j)) /
        ∑ l, Real.exp (-‖k l‖ ^ 2) * Real.exp (2 * inner ℝ q (k l)) := by sorry

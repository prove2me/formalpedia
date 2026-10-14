-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxBorn_coherentBorn_eq_softmax
-- name    : BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:28:53.665208+00:00
-- url     : https://prove2.me/theorems/9d82ad53-11af-4c67-a1c5-045324d73e03
-- title:
--   `BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) : bornWeight
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxBorn`.
--
--   `BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) : bornWeight q k j = softmax 2 q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax`.

-- Generated from ChapterSoftmaxBorn.lean — theorem BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) :
    bornWeight q k j = softmax 2 q k j := by sorry

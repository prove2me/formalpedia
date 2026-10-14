-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxBorn_coherentBorn_eq_softmax_of_unit_keys
-- name    : BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax_of_unit_keys
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:09:29.704017+00:00
-- url     : https://prove2.me/theorems/8caeec1b-fe6b-4fd1-bef7-872e10488930
-- title:
--   `BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax_of_unit_keys` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (hk : ∀ l, ‖k l‖ = 1) (j : Fin m) : bornWe
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxBorn`.
--
--   `BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax_of_unit_keys` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (hk : ∀ l, ‖k l‖ = 1) (j : Fin m) : bornWeight q k j = softmax 2 q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax_of_unit_keys`.

-- Generated from ChapterSoftmaxBorn.lean — theorem BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax_of_unit_keys
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax_of_unit_keys (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (hk : ∀ l, ‖k l‖ = 1) (j : Fin m) :
    bornWeight q k j = softmax 2 q k j := by sorry

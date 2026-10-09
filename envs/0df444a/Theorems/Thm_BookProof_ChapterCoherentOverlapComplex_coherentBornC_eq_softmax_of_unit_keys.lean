-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_coherentBornC_eq_softmax_of_unit_keys
-- name    : BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax_of_unit_keys
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:02:42.594802+00:00
-- url     : https://prove2.me/theorems/f6be9fb3-04a3-47c8-b6b0-d54fb6f91b63
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax_of_unit_keys` (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (hk : ∀ l, ‖k l‖ = 1) (j : Fin
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax_of_unit_keys` (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (hk : ∀ l, ‖k l‖ = 1) (j : Fin m) : bornWeightC q k j = softmaxC 2 q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax_of_unit_keys`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax_of_unit_keys
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax_of_unit_keys (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (hk : ∀ l, ‖k l‖ = 1) (j : Fin m) :
    bornWeightC q k j = softmaxC 2 q k j := by sorry

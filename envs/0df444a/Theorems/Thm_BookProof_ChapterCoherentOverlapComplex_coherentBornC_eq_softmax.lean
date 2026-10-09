-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_coherentBornC_eq_softmax
-- name    : BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:02:50.517314+00:00
-- url     : https://prove2.me/theorems/49bfc609-61cb-4267-97bb-84626c534827
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax` (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax` (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) : bornWeightC q k j = softmaxC 2 q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) :
    bornWeightC q k j = softmaxC 2 q k j := by sorry

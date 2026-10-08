-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentFidelity_bornWeightC_eq_scoreSoftmax_neg_dist_sq
-- name    : BookProof.ChapterCoherentFidelity.bornWeightC_eq_scoreSoftmax_neg_dist_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:51:22.056746+00:00
-- url     : https://prove2.me/theorems/97c23525-55a6-4b49-a748-5b3a18c98dee
-- title:
--   `BookProof.ChapterCoherentFidelity.bornWeightC_eq_scoreSoftmax_neg_dist_sq` (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : bornWeightC q k j =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentFidelity`.
--
--   `BookProof.ChapterCoherentFidelity.bornWeightC_eq_scoreSoftmax_neg_dist_sq` (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : bornWeightC q k j = scoreSoftmax 1 (fun l => -‖q - k l‖ ^ 2) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentFidelity.bornWeightC_eq_scoreSoftmax_neg_dist_sq`.

-- Generated from ChapterCoherentFidelity.lean — theorem BookProof.ChapterCoherentFidelity.bornWeightC_eq_scoreSoftmax_neg_dist_sq
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
import Definitions.Def_ChapterCoherentOverlapComplex
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterCoherentOverlapComplex
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterCoherentFidelity


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

theorem BookProof.ChapterCoherentFidelity.bornWeightC_eq_scoreSoftmax_neg_dist_sq (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    bornWeightC q k j = scoreSoftmax 1 (fun l => -‖q - k l‖ ^ 2) j := by sorry

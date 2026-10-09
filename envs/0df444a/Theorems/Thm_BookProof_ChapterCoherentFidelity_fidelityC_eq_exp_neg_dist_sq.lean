-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_eq_exp_neg_dist_sq
-- name    : BookProof.ChapterCoherentFidelity.fidelityC_eq_exp_neg_dist_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:49:57.570205+00:00
-- url     : https://prove2.me/theorems/f2923088-3992-4bad-bdc1-6532b7b3ace3
-- title:
--   `BookProof.ChapterCoherentFidelity.fidelityC_eq_exp_neg_dist_sq` (q k : EuclideanSpace ℂ (Fin n)) : fidelityC q k = Real.exp (-‖q - k‖ ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentFidelity`.
--
--   `BookProof.ChapterCoherentFidelity.fidelityC_eq_exp_neg_dist_sq` (q k : EuclideanSpace ℂ (Fin n)) : fidelityC q k = Real.exp (-‖q - k‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentFidelity.fidelityC_eq_exp_neg_dist_sq`.

-- Generated from ChapterCoherentFidelity.lean — theorem BookProof.ChapterCoherentFidelity.fidelityC_eq_exp_neg_dist_sq
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentFidelity


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

theorem BookProof.ChapterCoherentFidelity.fidelityC_eq_exp_neg_dist_sq (q k : EuclideanSpace ℂ (Fin n)) :
    fidelityC q k = Real.exp (-‖q - k‖ ^ 2) := by sorry

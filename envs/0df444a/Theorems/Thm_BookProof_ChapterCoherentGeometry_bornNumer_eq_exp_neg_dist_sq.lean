-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentGeometry_bornNumer_eq_exp_neg_dist_sq
-- name    : BookProof.ChapterCoherentGeometry.bornNumer_eq_exp_neg_dist_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:52:23.025576+00:00
-- url     : https://prove2.me/theorems/f2edecbb-4ec0-4b52-a039-4054fcec7502
-- title:
--   `BookProof.ChapterCoherentGeometry.bornNumer_eq_exp_neg_dist_sq` (q k : EuclideanSpace ℝ (Fin n)) : bornNumer q k = Real.exp (-‖q - k‖ ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentGeometry`.
--
--   `BookProof.ChapterCoherentGeometry.bornNumer_eq_exp_neg_dist_sq` (q k : EuclideanSpace ℝ (Fin n)) : bornNumer q k = Real.exp (-‖q - k‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentGeometry.bornNumer_eq_exp_neg_dist_sq`.

-- Generated from ChapterCoherentGeometry.lean — theorem BookProof.ChapterCoherentGeometry.bornNumer_eq_exp_neg_dist_sq
import Mathlib
import Definitions.Def_ChapterCoherentGeometry
import Definitions.Def_ChapterCoherentOverlap
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterCoherentGeometry


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterCoherentGeometry.bornNumer_eq_exp_neg_dist_sq (q k : EuclideanSpace ℝ (Fin n)) :
    bornNumer q k = Real.exp (-‖q - k‖ ^ 2) := by sorry

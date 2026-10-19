-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentGeometry_bornWeight_eq_scoreSoftmax_neg_dist_sq
-- name    : BookProof.ChapterCoherentGeometry.bornWeight_eq_scoreSoftmax_neg_dist_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:45:33.882121+00:00
-- url     : https://prove2.me/theorems/44d68b0f-5cdc-4a9e-a2f8-6bc48a753ef8
-- title:
--   `BookProof.ChapterCoherentGeometry.bornWeight_eq_scoreSoftmax_neg_dist_sq` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : bornWeight q k j = sc
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentGeometry`.
--
--   `BookProof.ChapterCoherentGeometry.bornWeight_eq_scoreSoftmax_neg_dist_sq` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : bornWeight q k j = scoreSoftmax 1 (fun l => -‖q - k l‖ ^ 2) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentGeometry.bornWeight_eq_scoreSoftmax_neg_dist_sq`.

-- Generated from ChapterCoherentGeometry.lean — theorem BookProof.ChapterCoherentGeometry.bornWeight_eq_scoreSoftmax_neg_dist_sq
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterCoherentGeometry
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterCoherentGeometry


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterCoherentGeometry.bornWeight_eq_scoreSoftmax_neg_dist_sq (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    bornWeight q k j = scoreSoftmax 1 (fun l => -‖q - k l‖ ^ 2) j := by sorry

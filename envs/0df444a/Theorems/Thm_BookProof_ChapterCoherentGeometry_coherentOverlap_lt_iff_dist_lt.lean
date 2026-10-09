-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentGeometry_coherentOverlap_lt_iff_dist_lt
-- name    : BookProof.ChapterCoherentGeometry.coherentOverlap_lt_iff_dist_lt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:52:12.337508+00:00
-- url     : https://prove2.me/theorems/5b71f7e4-ac3a-41d1-9f8e-f066990a0dae
-- title:
--   `BookProof.ChapterCoherentGeometry.coherentOverlap_lt_iff_dist_lt` (q k k' : EuclideanSpace ℝ (Fin n)) : coherentOverlap q k < coherentOverlap q k' ↔ ‖q - k'‖ < ‖q - k‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentGeometry`.
--
--   `BookProof.ChapterCoherentGeometry.coherentOverlap_lt_iff_dist_lt` (q k k' : EuclideanSpace ℝ (Fin n)) : coherentOverlap q k < coherentOverlap q k' ↔ ‖q - k'‖ < ‖q - k‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentGeometry.coherentOverlap_lt_iff_dist_lt`.

-- Generated from ChapterCoherentGeometry.lean — theorem BookProof.ChapterCoherentGeometry.coherentOverlap_lt_iff_dist_lt
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterCoherentGeometry
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterCoherentOverlap
open BookProof.ChapterCoherentGeometry


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterCoherentGeometry.coherentOverlap_lt_iff_dist_lt (q k k' : EuclideanSpace ℝ (Fin n)) :
    coherentOverlap q k < coherentOverlap q k' ↔ ‖q - k'‖ < ‖q - k‖ := by sorry

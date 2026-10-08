-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentGeometry_coherentOverlap_le_iff_dist_le
-- name    : BookProof.ChapterCoherentGeometry.coherentOverlap_le_iff_dist_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:52:03.267312+00:00
-- url     : https://prove2.me/theorems/e85ec242-9c83-4f69-b2a2-65b1b9e93040
-- title:
--   `BookProof.ChapterCoherentGeometry.coherentOverlap_le_iff_dist_le` (q k k' : EuclideanSpace ℝ (Fin n)) : coherentOverlap q k ≤ coherentOverlap q k' ↔ ‖q - k'‖ ≤ ‖q - k‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentGeometry`.
--
--   `BookProof.ChapterCoherentGeometry.coherentOverlap_le_iff_dist_le` (q k k' : EuclideanSpace ℝ (Fin n)) : coherentOverlap q k ≤ coherentOverlap q k' ↔ ‖q - k'‖ ≤ ‖q - k‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentGeometry.coherentOverlap_le_iff_dist_le`.

-- Generated from ChapterCoherentGeometry.lean — theorem BookProof.ChapterCoherentGeometry.coherentOverlap_le_iff_dist_le
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

theorem BookProof.ChapterCoherentGeometry.coherentOverlap_le_iff_dist_le (q k k' : EuclideanSpace ℝ (Fin n)) :
    coherentOverlap q k ≤ coherentOverlap q k' ↔ ‖q - k'‖ ≤ ‖q - k‖ := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentGeometry_neg_two_mul_log_coherentOverlap
-- name    : BookProof.ChapterCoherentGeometry.neg_two_mul_log_coherentOverlap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:51:57.746278+00:00
-- url     : https://prove2.me/theorems/6ab99028-657b-443f-8428-15a1e51e8e46
-- title:
--   `BookProof.ChapterCoherentGeometry.neg_two_mul_log_coherentOverlap` (q k : EuclideanSpace ℝ (Fin n)) : -2 * Real.log (coherentOverlap q k) = ‖q - k‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentGeometry`.
--
--   `BookProof.ChapterCoherentGeometry.neg_two_mul_log_coherentOverlap` (q k : EuclideanSpace ℝ (Fin n)) : -2 * Real.log (coherentOverlap q k) = ‖q - k‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentGeometry.neg_two_mul_log_coherentOverlap`.

-- Generated from ChapterCoherentGeometry.lean — theorem BookProof.ChapterCoherentGeometry.neg_two_mul_log_coherentOverlap
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

theorem BookProof.ChapterCoherentGeometry.neg_two_mul_log_coherentOverlap (q k : EuclideanSpace ℝ (Fin n)) :
    -2 * Real.log (coherentOverlap q k) = ‖q - k‖ ^ 2 := by sorry

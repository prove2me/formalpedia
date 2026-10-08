-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentGeometry_bornWeight_le_iff_dist_le
-- name    : BookProof.ChapterCoherentGeometry.bornWeight_le_iff_dist_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:52:29.50498+00:00
-- url     : https://prove2.me/theorems/943a8042-cc54-4ed8-8a61-1cd9af2194d8
-- title:
--   `BookProof.ChapterCoherentGeometry.bornWeight_le_iff_dist_le` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (i j : Fin m) : bornWeight q k i ≤ bornWeight q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentGeometry`.
--
--   `BookProof.ChapterCoherentGeometry.bornWeight_le_iff_dist_le` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (i j : Fin m) : bornWeight q k i ≤ bornWeight q k j ↔ ‖q - k j‖ ≤ ‖q - k i‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentGeometry.bornWeight_le_iff_dist_le`.

-- Generated from ChapterCoherentGeometry.lean — theorem BookProof.ChapterCoherentGeometry.bornWeight_le_iff_dist_le
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

theorem BookProof.ChapterCoherentGeometry.bornWeight_le_iff_dist_le (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (i j : Fin m) :
    bornWeight q k i ≤ bornWeight q k j ↔ ‖q - k j‖ ≤ ‖q - k i‖ := by sorry

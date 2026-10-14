-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentGeometry_bornWeight_max_of_nearest
-- name    : BookProof.ChapterCoherentGeometry.bornWeight_max_of_nearest
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:45:39.781702+00:00
-- url     : https://prove2.me/theorems/670df600-1b28-41aa-ab05-46783307f250
-- title:
--   `BookProof.ChapterCoherentGeometry.bornWeight_max_of_nearest` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) (hj : ∀ l, ‖q - k j‖ ≤ ‖q - k l‖) (i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentGeometry`.
--
--   `BookProof.ChapterCoherentGeometry.bornWeight_max_of_nearest` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) (hj : ∀ l, ‖q - k j‖ ≤ ‖q - k l‖) (i : Fin m) : bornWeight q k i ≤ bornWeight q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentGeometry.bornWeight_max_of_nearest`.

-- Generated from ChapterCoherentGeometry.lean — theorem BookProof.ChapterCoherentGeometry.bornWeight_max_of_nearest
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterCoherentGeometry
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterCoherentGeometry


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterCoherentGeometry.bornWeight_max_of_nearest (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m)
    (hj : ∀ l, ‖q - k j‖ ≤ ‖q - k l‖) (i : Fin m) :
    bornWeight q k i ≤ bornWeight q k j := by sorry

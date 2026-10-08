-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldSphereSupport_sphereGaussian_sphere_eq_one
-- name    : BookProof.ChapterFreeFieldSphereSupport.sphereGaussian_sphere_eq_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T05:00:55.865906+00:00
-- url     : https://prove2.me/theorems/8ad8d14e-2126-449e-a755-c6c67e5bae03
-- title:
--   `BookProof.ChapterFreeFieldSphereSupport.sphereGaussian_sphere_eq_one` (hn : 0 < n) : sphereGaussian n (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldSphereSupport`.
--
--   `BookProof.ChapterFreeFieldSphereSupport.sphereGaussian_sphere_eq_one` (hn : 0 < n) : sphereGaussian n (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldSphereSupport.sphereGaussian_sphere_eq_one`.

-- Generated from ChapterFreeFieldSphereSupport.lean — theorem BookProof.ChapterFreeFieldSphereSupport.sphereGaussian_sphere_eq_one
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Mathlib
import Definitions.Def_ChapterFreeFieldSphereSupport
open BookProof.ChapterFreeFieldSphereSupport

variable {n : ℕ}


open MeasureTheory ProbabilityTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere

theorem BookProof.ChapterFreeFieldSphereSupport.sphereGaussian_sphere_eq_one (hn : 0 < n) :
    sphereGaussian n (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) = 1 := by sorry

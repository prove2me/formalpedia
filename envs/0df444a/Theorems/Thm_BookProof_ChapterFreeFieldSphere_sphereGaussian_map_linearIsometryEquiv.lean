-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldSphere_sphereGaussian_map_linearIsometryEquiv
-- name    : BookProof.ChapterFreeFieldSphere.sphereGaussian_map_linearIsometryEquiv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T04:41:32.642094+00:00
-- url     : https://prove2.me/theorems/f6fe0538-80ef-48e1-ad6c-47febb1a56c5
-- title:
--   `BookProof.ChapterFreeFieldSphere.sphereGaussian_map_linearIsometryEquiv` (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) : (sphereGaussian n).map L = sphereGaussian
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldSphere`.
--
--   `BookProof.ChapterFreeFieldSphere.sphereGaussian_map_linearIsometryEquiv` (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) : (sphereGaussian n).map L = sphereGaussian n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldSphere.sphereGaussian_map_linearIsometryEquiv`.

-- Generated from ChapterFreeFieldSphere.lean — theorem BookProof.ChapterFreeFieldSphere.sphereGaussian_map_linearIsometryEquiv
import Definitions.Def_ChapterFreeFieldGaussian
import Mathlib
import Definitions.Def_ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphere

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldGaussian

theorem BookProof.ChapterFreeFieldSphere.sphereGaussian_map_linearIsometryEquiv
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (sphereGaussian n).map L = sphereGaussian n := by sorry

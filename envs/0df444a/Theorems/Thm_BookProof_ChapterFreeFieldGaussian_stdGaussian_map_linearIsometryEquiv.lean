-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldGaussian_stdGaussian_map_linearIsometryEquiv
-- name    : BookProof.ChapterFreeFieldGaussian.stdGaussian_map_linearIsometryEquiv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T04:20:47.591261+00:00
-- url     : https://prove2.me/theorems/cf027410-6226-4eb3-953c-a4aec96a6ae7
-- title:
--   `BookProof.ChapterFreeFieldGaussian.stdGaussian_map_linearIsometryEquiv` (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) : (stdGaussian n).map L = stdGaussian n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldGaussian`.
--
--   `BookProof.ChapterFreeFieldGaussian.stdGaussian_map_linearIsometryEquiv` (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) : (stdGaussian n).map L = stdGaussian n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldGaussian.stdGaussian_map_linearIsometryEquiv`.

-- Generated from ChapterFreeFieldGaussian.lean — theorem BookProof.ChapterFreeFieldGaussian.stdGaussian_map_linearIsometryEquiv
import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian
open BookProof.ChapterFreeFieldGaussian

variable {n : ℕ}


open MeasureTheory ProbabilityTheory Complex WithLp
open scoped RealInnerProductSpace ENNReal

theorem BookProof.ChapterFreeFieldGaussian.stdGaussian_map_linearIsometryEquiv
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (stdGaussian n).map L = stdGaussian n := by sorry

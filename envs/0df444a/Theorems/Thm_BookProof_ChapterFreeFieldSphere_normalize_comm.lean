-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldSphere_normalize_comm
-- name    : BookProof.ChapterFreeFieldSphere.normalize_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T04:21:14.884426+00:00
-- url     : https://prove2.me/theorems/dd91ac92-1087-42d2-9d22-e775524e0475
-- title:
--   `BookProof.ChapterFreeFieldSphere.normalize_comm` (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) : normalize (L x) = L (normalize x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldSphere`.
--
--   `BookProof.ChapterFreeFieldSphere.normalize_comm` (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) : normalize (L x) = L (normalize x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldSphere.normalize_comm`.

-- Generated from ChapterFreeFieldSphere.lean — theorem BookProof.ChapterFreeFieldSphere.normalize_comm
import Definitions.Def_ChapterFreeFieldGaussian
import Mathlib
import Definitions.Def_ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphere

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldGaussian

theorem BookProof.ChapterFreeFieldSphere.normalize_comm (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : normalize (L x) = L (normalize x) := by sorry

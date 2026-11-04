-- Prove2me | Theorems.Thm_BookProof_ChapterG3_mehler_uniform_gauge_invariant
-- name    : BookProof.ChapterG3.mehler_uniform_gauge_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T13:45:19.961149+00:00
-- url     : https://prove2.me/theorems/0ec66249-c4c7-4f2a-9c92-76a89dbc4475
-- title:
--   `BookProof.ChapterG3.mehler_uniform_gauge_invariant` (k : ℕ) (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) : (PhysHSGaussian.sphereUniform k).map L = PhysHSGaussia
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG3`.
--
--   `BookProof.ChapterG3.mehler_uniform_gauge_invariant` (k : ℕ) (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) : (PhysHSGaussian.sphereUniform k).map L = PhysHSGaussian.sphereUniform k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG3.mehler_uniform_gauge_invariant`.

-- Generated from ChapterG3.lean — theorem BookProof.ChapterG3.mehler_uniform_gauge_invariant
import Mathlib
import Definitions.Def_ChapterG3
import Definitions.Def_ChapterG3Promoted
open BookProof.ChapterG3


open MeasureTheory
open scoped ENNReal



variable {X : Type*}

theorem BookProof.ChapterG3.mehler_uniform_gauge_invariant (k : ℕ)
    (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    (PhysHSGaussian.sphereUniform k).map L = PhysHSGaussian.sphereUniform k := by sorry

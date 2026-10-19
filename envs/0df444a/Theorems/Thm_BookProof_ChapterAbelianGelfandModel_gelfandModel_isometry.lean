-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianGelfandModel_gelfandModel_isometry
-- name    : BookProof.ChapterAbelianGelfandModel.gelfandModel_isometry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:20:21.270467+00:00
-- url     : https://prove2.me/theorems/8c483067-bb96-49bc-8dc3-be38d2652382
-- title:
--   `BookProof.ChapterAbelianGelfandModel.gelfandModel_isometry` : Isometry (gelfandModel A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianGelfandModel`.
--
--   `BookProof.ChapterAbelianGelfandModel.gelfandModel_isometry` : Isometry (gelfandModel A)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianGelfandModel.gelfandModel_isometry`.

-- Generated from ChapterAbelianGelfandModel.lean — theorem BookProof.ChapterAbelianGelfandModel.gelfandModel_isometry
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel
open BookProof.ChapterAbelianGelfandModel


open MeasureTheory Complex WeakDual CompactlySupported CompactlySupportedContinuousMap
open scoped ComplexOrder


open BookProof.ChapterLinftyMultiplication

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {X : Type*} [TopologicalSpace X]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  (psi : C(X, ℂ) →ₗ[ℂ] ℂ) (hpos : ∀ g : C(X, ℂ), 0 ≤ psi (star g * g))
variable {X : Type*} [MeasurableSpace X] (mu : Measure X)
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (mu : Measure X)
variable (A : Type*) [CommCStarAlgebra A]

theorem BookProof.ChapterAbelianGelfandModel.gelfandModel_isometry : Isometry (gelfandModel A) := by sorry

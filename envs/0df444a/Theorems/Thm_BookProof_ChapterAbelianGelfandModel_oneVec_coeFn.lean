-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianGelfandModel_oneVec_coeFn
-- name    : BookProof.ChapterAbelianGelfandModel.oneVec_coeFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:19:38.093918+00:00
-- url     : https://prove2.me/theorems/03cb3baa-adf0-4d57-bbbf-41c830c89002
-- title:
--   `BookProof.ChapterAbelianGelfandModel.oneVec_coeFn` [IsFiniteMeasure mu] : (oneVec mu : X → ℂ) =ᵐ[mu] fun _ => (1 : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianGelfandModel`.
--
--   `BookProof.ChapterAbelianGelfandModel.oneVec_coeFn` [IsFiniteMeasure mu] : (oneVec mu : X → ℂ) =ᵐ[mu] fun _ => (1 : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianGelfandModel.oneVec_coeFn`.

-- Generated from ChapterAbelianGelfandModel.lean — theorem BookProof.ChapterAbelianGelfandModel.oneVec_coeFn
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

theorem BookProof.ChapterAbelianGelfandModel.oneVec_coeFn [IsFiniteMeasure mu] : (oneVec mu : X → ℂ) =ᵐ[mu] fun _ => (1 : ℂ) := by sorry

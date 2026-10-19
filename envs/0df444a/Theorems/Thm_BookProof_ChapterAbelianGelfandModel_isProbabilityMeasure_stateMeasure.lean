-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianGelfandModel_isProbabilityMeasure_stateMeasure
-- name    : BookProof.ChapterAbelianGelfandModel.isProbabilityMeasure_stateMeasure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:19:15.013982+00:00
-- url     : https://prove2.me/theorems/7798d8ef-a123-4465-a480-f6f3381bb177
-- title:
--   `BookProof.ChapterAbelianGelfandModel.isProbabilityMeasure_stateMeasure` (hone : psi 1 = 1) : IsProbabilityMeasure (stateMeasure psi hpos)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianGelfandModel`.
--
--   `BookProof.ChapterAbelianGelfandModel.isProbabilityMeasure_stateMeasure` (hone : psi 1 = 1) : IsProbabilityMeasure (stateMeasure psi hpos)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianGelfandModel.isProbabilityMeasure_stateMeasure`.

-- Generated from ChapterAbelianGelfandModel.lean — theorem BookProof.ChapterAbelianGelfandModel.isProbabilityMeasure_stateMeasure
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterA3b
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

theorem BookProof.ChapterAbelianGelfandModel.isProbabilityMeasure_stateMeasure (hone : psi 1 = 1) :
    IsProbabilityMeasure (stateMeasure psi hpos) := by sorry

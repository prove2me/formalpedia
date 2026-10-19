-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianGelfandModel_integral_stateMeasure
-- name    : BookProof.ChapterAbelianGelfandModel.integral_stateMeasure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:21:16.87643+00:00
-- url     : https://prove2.me/theorems/e0d1fdbd-d71c-42ba-a5e2-be1334220312
-- title:
--   `BookProof.ChapterAbelianGelfandModel.integral_stateMeasure` (g : C(X, ℂ)) : psi g = ∫ x, g x ∂(stateMeasure psi hpos)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianGelfandModel`.
--
--   `BookProof.ChapterAbelianGelfandModel.integral_stateMeasure` (g : C(X, ℂ)) : psi g = ∫ x, g x ∂(stateMeasure psi hpos)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianGelfandModel.integral_stateMeasure`.

-- Generated from ChapterAbelianGelfandModel.lean — theorem BookProof.ChapterAbelianGelfandModel.integral_stateMeasure
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

theorem BookProof.ChapterAbelianGelfandModel.integral_stateMeasure (g : C(X, ℂ)) :
    psi g = ∫ x, g x ∂(stateMeasure psi hpos) := by sorry

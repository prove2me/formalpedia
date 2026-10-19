-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicModel_isProbabilityMeasure_repMeasure
-- name    : BookProof.ChapterAbelianCyclicModel.isProbabilityMeasure_repMeasure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:21:14.162975+00:00
-- url     : https://prove2.me/theorems/d0a69089-e126-44e9-9e84-70b02b079739
-- title:
--   `BookProof.ChapterAbelianCyclicModel.isProbabilityMeasure_repMeasure` (hxi : ‖xi‖ = 1) : IsProbabilityMeasure (repMeasure pi xi)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicModel`.
--
--   `BookProof.ChapterAbelianCyclicModel.isProbabilityMeasure_repMeasure` (hxi : ‖xi‖ = 1) : IsProbabilityMeasure (repMeasure pi xi)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicModel.isProbabilityMeasure_repMeasure`.

-- Generated from ChapterAbelianCyclicModel.lean — theorem BookProof.ChapterAbelianCyclicModel.isProbabilityMeasure_repMeasure
import Definitions.Def_ChapterAbelianGelfandModel
import Mathlib
import Definitions.Def_ChapterAbelianCyclicModel
open BookProof.ChapterAbelianCyclicModel


open MeasureTheory Complex WeakDual
open scoped ComplexOrder


open BookProof.ChapterAbelianGelfandModel


variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)

theorem BookProof.ChapterAbelianCyclicModel.isProbabilityMeasure_repMeasure (hxi : ‖xi‖ = 1) :
    IsProbabilityMeasure (repMeasure pi xi) := by sorry

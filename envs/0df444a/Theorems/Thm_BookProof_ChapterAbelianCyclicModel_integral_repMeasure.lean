-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicModel_integral_repMeasure
-- name    : BookProof.ChapterAbelianCyclicModel.integral_repMeasure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:21:13.084007+00:00
-- url     : https://prove2.me/theorems/5d7b7ac6-fa60-4bef-876f-05b05f2675e7
-- title:
--   `BookProof.ChapterAbelianCyclicModel.integral_repMeasure` (f : C(X, ℂ)) : inner ℂ xi (pi f xi) = ∫ x, f x ∂(repMeasure pi xi)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicModel`.
--
--   `BookProof.ChapterAbelianCyclicModel.integral_repMeasure` (f : C(X, ℂ)) : inner ℂ xi (pi f xi) = ∫ x, f x ∂(repMeasure pi xi)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicModel.integral_repMeasure`.

-- Generated from ChapterAbelianCyclicModel.lean — theorem BookProof.ChapterAbelianCyclicModel.integral_repMeasure
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

theorem BookProof.ChapterAbelianCyclicModel.integral_repMeasure (f : C(X, ℂ)) :
    inner ℂ xi (pi f xi) = ∫ x, f x ∂(repMeasure pi xi) := by sorry

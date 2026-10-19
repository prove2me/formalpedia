-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicModel_mulRep_toLp
-- name    : BookProof.ChapterAbelianCyclicModel.mulRep_toLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:21:38.063974+00:00
-- url     : https://prove2.me/theorems/e9f5828e-09a2-4045-b04d-869d4f043ff2
-- title:
--   `BookProof.ChapterAbelianCyclicModel.mulRep_toLp` (g f : C(X, ℂ)) : mulRep (repMeasure pi xi) g (ContinuousMap.toLp 2 (repMeasure pi xi) ℂ f) = ContinuousMap.toLp 2 (repMeasure pi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicModel`.
--
--   `BookProof.ChapterAbelianCyclicModel.mulRep_toLp` (g f : C(X, ℂ)) : mulRep (repMeasure pi xi) g (ContinuousMap.toLp 2 (repMeasure pi xi) ℂ f) = ContinuousMap.toLp 2 (repMeasure pi xi) ℂ (g * f)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicModel.mulRep_toLp`.

-- Generated from ChapterAbelianCyclicModel.lean — theorem BookProof.ChapterAbelianCyclicModel.mulRep_toLp
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

variable (hcyc : DenseRange (repVec pi xi))

theorem BookProof.ChapterAbelianCyclicModel.mulRep_toLp (g f : C(X, ℂ)) :
    mulRep (repMeasure pi xi) g (ContinuousMap.toLp 2 (repMeasure pi xi) ℂ f)
      = ContinuousMap.toLp 2 (repMeasure pi xi) ℂ (g * f) := by sorry

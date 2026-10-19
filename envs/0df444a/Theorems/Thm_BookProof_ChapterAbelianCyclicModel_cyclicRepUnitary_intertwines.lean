-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicModel_cyclicRepUnitary_intertwines
-- name    : BookProof.ChapterAbelianCyclicModel.cyclicRepUnitary_intertwines
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:21:31.208105+00:00
-- url     : https://prove2.me/theorems/ff99ea81-e05c-4376-ad02-16e28f661413
-- title:
--   `BookProof.ChapterAbelianCyclicModel.cyclicRepUnitary_intertwines` (g : C(X, ℂ)) (u : Lp ℂ 2 (repMeasure pi xi)) : cyclicRepUnitary pi xi hcyc (mulRep (repMeasure pi xi) g u) = pi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicModel`.
--
--   `BookProof.ChapterAbelianCyclicModel.cyclicRepUnitary_intertwines` (g : C(X, ℂ)) (u : Lp ℂ 2 (repMeasure pi xi)) : cyclicRepUnitary pi xi hcyc (mulRep (repMeasure pi xi) g u) = pi g (cyclicRepUnitary pi xi hcyc u)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicModel.cyclicRepUnitary_intertwines`.

-- Generated from ChapterAbelianCyclicModel.lean — theorem BookProof.ChapterAbelianCyclicModel.cyclicRepUnitary_intertwines
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

theorem BookProof.ChapterAbelianCyclicModel.cyclicRepUnitary_intertwines (g : C(X, ℂ)) (u : Lp ℂ 2 (repMeasure pi xi)) :
    cyclicRepUnitary pi xi hcyc (mulRep (repMeasure pi xi) g u)
      = pi g (cyclicRepUnitary pi xi hcyc u) := by sorry

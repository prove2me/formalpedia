-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeCasimirAverage_gaugeAverage_of_isPhysicalObservable
-- name    : BookProof.ChapterGaugeCasimirAverage.gaugeAverage_of_isPhysicalObservable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:54:34.030789+00:00
-- url     : https://prove2.me/theorems/4c3bef7a-1f95-4ed7-9f84-51c34d8a248f
-- title:
--   `BookProof.ChapterGaugeCasimirAverage.gaugeAverage_of_isPhysicalObservable` (μ : Measure G) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : IsPhysicalObservable G f) : gaugeAverage (X :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeCasimirAverage`.
--
--   `BookProof.ChapterGaugeCasimirAverage.gaugeAverage_of_isPhysicalObservable` (μ : Measure G) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : IsPhysicalObservable G f) : gaugeAverage (X := X) μ f = f
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeCasimirAverage.gaugeAverage_of_isPhysicalObservable`.

-- Generated from ChapterGaugeCasimirAverage.lean — theorem BookProof.ChapterGaugeCasimirAverage.gaugeAverage_of_isPhysicalObservable
import Mathlib
import Definitions.Def_ChapterGaugeCasimirAverage
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeCasimirAverage



open BookProof.ChapterGaugeIncompleteFixing
open MeasureTheory
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {ι : Type*} [Fintype ι]
variable {X : Type*}
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MulAction G X]

theorem BookProof.ChapterGaugeCasimirAverage.gaugeAverage_of_isPhysicalObservable (μ : Measure G) [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : IsPhysicalObservable G f) :
    gaugeAverage (X := X) μ f = f := by sorry

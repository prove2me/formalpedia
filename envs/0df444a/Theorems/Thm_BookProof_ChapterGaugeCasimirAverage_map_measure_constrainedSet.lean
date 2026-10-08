-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeCasimirAverage_map_measure_constrainedSet
-- name    : BookProof.ChapterGaugeCasimirAverage.map_measure_constrainedSet
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:56:27.110264+00:00
-- url     : https://prove2.me/theorems/e0384593-e83e-425d-aef1-60af8c3ddccc
-- title:
--   `BookProof.ChapterGaugeCasimirAverage.map_measure_constrainedSet` (μ : Measure X) [IsProbabilityMeasure μ] {C : Set X} (hC : MeasurableSet C) {q : X → X} (hq : Measurable q) (hqC :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeCasimirAverage`.
--
--   `BookProof.ChapterGaugeCasimirAverage.map_measure_constrainedSet` (μ : Measure X) [IsProbabilityMeasure μ] {C : Set X} (hC : MeasurableSet C) {q : X → X} (hq : Measurable q) (hqC : ∀ x, q x ∈ C) : (μ.map q) C = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeCasimirAverage.map_measure_constrainedSet`.

-- Generated from ChapterGaugeCasimirAverage.lean — theorem BookProof.ChapterGaugeCasimirAverage.map_measure_constrainedSet
import Definitions.Def_ChapterGaugeIncompleteFixing
import Mathlib
import Definitions.Def_ChapterGaugeCasimirAverage
open BookProof.ChapterGaugeCasimirAverage



open BookProof.ChapterGaugeIncompleteFixing
open MeasureTheory
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {ι : Type*} [Fintype ι]
variable {X : Type*}
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [Fintype G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [MulAction G X]
variable {X : Type*} [MeasurableSpace X]

theorem BookProof.ChapterGaugeCasimirAverage.map_measure_constrainedSet (μ : Measure X) [IsProbabilityMeasure μ]
    {C : Set X} (hC : MeasurableSet C) {q : X → X} (hq : Measurable q)
    (hqC : ∀ x, q x ∈ C) : (μ.map q) C = 1 := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeCasimirAverage_physical_invariant_along_gaugeProjection
-- name    : BookProof.ChapterGaugeCasimirAverage.physical_invariant_along_gaugeProjection
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:55:22.722833+00:00
-- url     : https://prove2.me/theorems/2dd39d6e-1daf-413f-9165-3a0b0c411e95
-- title:
--   `BookProof.ChapterGaugeCasimirAverage.physical_invariant_along_gaugeProjection` {G : Type*} [Group G] [MulAction G X] {f : X → ℝ} (hf : IsPhysicalObservable G f) {q : X → X} (hq :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeCasimirAverage`.
--
--   `BookProof.ChapterGaugeCasimirAverage.physical_invariant_along_gaugeProjection` {G : Type*} [Group G] [MulAction G X] {f : X → ℝ} (hf : IsPhysicalObservable G f) {q : X → X} (hq : ∀ x, ∃ g : G, q x = g • x) (x : X) : f (q x) = f x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeCasimirAverage.physical_invariant_along_gaugeProjection`.

-- Generated from ChapterGaugeCasimirAverage.lean — theorem BookProof.ChapterGaugeCasimirAverage.physical_invariant_along_gaugeProjection
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
variable {X : Type*} {G : Type*} [Group G] [Fintype G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [MulAction G X]
variable {X : Type*} [MeasurableSpace X]

theorem BookProof.ChapterGaugeCasimirAverage.physical_invariant_along_gaugeProjection {G : Type*} [Group G] [MulAction G X]
    {f : X → ℝ} (hf : IsPhysicalObservable G f) {q : X → X}
    (hq : ∀ x, ∃ g : G, q x = g • x) (x : X) : f (q x) = f x := by sorry

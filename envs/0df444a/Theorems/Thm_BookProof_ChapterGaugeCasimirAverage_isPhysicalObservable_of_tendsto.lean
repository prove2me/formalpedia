-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeCasimirAverage_isPhysicalObservable_of_tendsto
-- name    : BookProof.ChapterGaugeCasimirAverage.isPhysicalObservable_of_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:55:00.862984+00:00
-- url     : https://prove2.me/theorems/1d0921f5-7022-4bbf-8460-b2970798e29b
-- title:
--   `BookProof.ChapterGaugeCasimirAverage.isPhysicalObservable_of_tendsto` {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → X → ℝ} (hf : ∀ i, IsPhysicalObservable G (f i)) {F : X → ℝ} (h
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeCasimirAverage`.
--
--   `BookProof.ChapterGaugeCasimirAverage.isPhysicalObservable_of_tendsto` {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → X → ℝ} (hf : ∀ i, IsPhysicalObservable G (f i)) {F : X → ℝ} (h : ∀ x, Filter.Tendsto (fun i => f i x) l (nhds (F x))) : IsPhysicalObservable G F
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeCasimirAverage.isPhysicalObservable_of_tendsto`.

-- Generated from ChapterGaugeCasimirAverage.lean — theorem BookProof.ChapterGaugeCasimirAverage.isPhysicalObservable_of_tendsto
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

theorem BookProof.ChapterGaugeCasimirAverage.isPhysicalObservable_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → X → ℝ} (hf : ∀ i, IsPhysicalObservable G (f i)) {F : X → ℝ}
    (h : ∀ x, Filter.Tendsto (fun i => f i x) l (nhds (F x))) :
    IsPhysicalObservable G F := by sorry

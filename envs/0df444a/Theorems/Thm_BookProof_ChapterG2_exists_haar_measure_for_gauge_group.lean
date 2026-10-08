-- Prove2me | Theorems.Thm_BookProof_ChapterG2_exists_haar_measure_for_gauge_group
-- name    : BookProof.ChapterG2.exists_haar_measure_for_gauge_group
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:51:15.354146+00:00
-- url     : https://prove2.me/theorems/2f929dc6-a754-441b-bd91-76482bf5e4eb
-- title:
--   `BookProof.ChapterG2.exists_haar_measure_for_gauge_group` (G : Type*) [MeasurableSpace G] [TopologicalSpace G] [LocallyCompactSpace G] [Group G] [BorelSpace G] [IsTopologicalGroup
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG2`.
--
--   `BookProof.ChapterG2.exists_haar_measure_for_gauge_group` (G : Type*) [MeasurableSpace G] [TopologicalSpace G] [LocallyCompactSpace G] [Group G] [BorelSpace G] [IsTopologicalGroup G] : ∃ (μ : Measure G), μ.IsHaarMeasure
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG2.exists_haar_measure_for_gauge_group`.

-- Generated from ChapterG2.lean — theorem BookProof.ChapterG2.exists_haar_measure_for_gauge_group
import Mathlib
import Definitions.Def_ChapterG2
open BookProof.ChapterG2


open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : Type*} [CommRing A] (Q : A)
variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

theorem BookProof.ChapterG2.exists_haar_measure_for_gauge_group (G : Type*)
    [MeasurableSpace G] [TopologicalSpace G] [LocallyCompactSpace G] [Group G]
    [BorelSpace G] [IsTopologicalGroup G] :
    ∃ (μ : Measure G), μ.IsHaarMeasure := by sorry

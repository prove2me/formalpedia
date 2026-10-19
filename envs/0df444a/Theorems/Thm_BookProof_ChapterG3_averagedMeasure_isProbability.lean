-- Prove2me | Theorems.Thm_BookProof_ChapterG3_averagedMeasure_isProbability
-- name    : BookProof.ChapterG3.averagedMeasure_isProbability
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T11:35:47.635878+00:00
-- url     : https://prove2.me/theorems/ca44d4c8-3fec-4d5d-9189-d55c257c4df1
-- title:
--   `BookProof.ChapterG3.averagedMeasure_isProbability` (G : Type*) [Group G] [Fintype G] {Z : Type*} [MeasurableSpace Z] [MulAction G Z] (hmeas : ∀ g : G, Measurable (fun x : Z => g •
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG3`.
--
--   `BookProof.ChapterG3.averagedMeasure_isProbability` (G : Type*) [Group G] [Fintype G] {Z : Type*} [MeasurableSpace Z] [MulAction G Z] (hmeas : ∀ g : G, Measurable (fun x : Z => g • x)) (μ : Measure Z) [IsProbabilityMeasure μ] : IsProbabilityMeasure (averagedMeasure G μ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG3.averagedMeasure_isProbability`.

-- Generated from ChapterG3.lean — theorem BookProof.ChapterG3.averagedMeasure_isProbability
import Mathlib
import Definitions.Def_ChapterG3
open BookProof.ChapterG3


open MeasureTheory
open scoped ENNReal



variable {X : Type*}

theorem BookProof.ChapterG3.averagedMeasure_isProbability (G : Type*) [Group G] [Fintype G]
    {Z : Type*} [MeasurableSpace Z] [MulAction G Z]
    (hmeas : ∀ g : G, Measurable (fun x : Z => g • x))
    (μ : Measure Z) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (averagedMeasure G μ) := by sorry

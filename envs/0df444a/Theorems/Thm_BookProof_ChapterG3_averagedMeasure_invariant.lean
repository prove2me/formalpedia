-- Prove2me | Theorems.Thm_BookProof_ChapterG3_averagedMeasure_invariant
-- name    : BookProof.ChapterG3.averagedMeasure_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T11:36:12.839121+00:00
-- url     : https://prove2.me/theorems/718a940c-930c-4e93-bc7d-53d2df8c72c1
-- title:
--   `BookProof.ChapterG3.averagedMeasure_invariant` (G : Type*) [Group G] [Fintype G] {Z : Type*} [MeasurableSpace Z] [MulAction G Z] (hmeas : ∀ g : G, Measurable (fun x : Z => g • x))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG3`.
--
--   `BookProof.ChapterG3.averagedMeasure_invariant` (G : Type*) [Group G] [Fintype G] {Z : Type*} [MeasurableSpace Z] [MulAction G Z] (hmeas : ∀ g : G, Measurable (fun x : Z => g • x)) (μ : Measure Z) (h : G) : (averagedMeasure G μ).map (fun x => h • x) = averagedMeasure G μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG3.averagedMeasure_invariant`.

-- Generated from ChapterG3.lean — theorem BookProof.ChapterG3.averagedMeasure_invariant
import Mathlib
import Definitions.Def_ChapterG3
open BookProof.ChapterG3


open MeasureTheory
open scoped ENNReal



variable {X : Type*}

theorem BookProof.ChapterG3.averagedMeasure_invariant (G : Type*) [Group G] [Fintype G]
    {Z : Type*} [MeasurableSpace Z] [MulAction G Z]
    (hmeas : ∀ g : G, Measurable (fun x : Z => g • x))
    (μ : Measure Z) (h : G) :
    (averagedMeasure G μ).map (fun x => h • x) = averagedMeasure G μ := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterG_gauge_constraint_pushforward_full_measure
-- name    : BookProof.ChapterG.gauge_constraint_pushforward_full_measure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:26:09.790725+00:00
-- url     : https://prove2.me/theorems/4cb912c8-4f9d-4468-8008-827f2a1a6130
-- title:
--   `BookProof.ChapterG.gauge_constraint_pushforward_full_measure` {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (q : X → X) (hq : Measurable q) (C : Set X)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG`.
--
--   `BookProof.ChapterG.gauge_constraint_pushforward_full_measure` {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (q : X → X) (hq : Measurable q) (C : Set X) (hC : MeasurableSet C) (hrange : ∀ x, q x ∈ C) : IsProbabilityMeasure (μ.map q) ∧ (μ.map q) C = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG.gauge_constraint_pushforward_full_measure`.

-- Generated from ChapterG.lean — theorem BookProof.ChapterG.gauge_constraint_pushforward_full_measure
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG


open scoped ComplexConjugate InnerProductSpace Matrix
open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

theorem BookProof.ChapterG.gauge_constraint_pushforward_full_measure
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → X) (hq : Measurable q)
    (C : Set X) (hC : MeasurableSet C)
    (hrange : ∀ x, q x ∈ C) :
    IsProbabilityMeasure (μ.map q) ∧ (μ.map q) C = 1 := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_eq_of_inner_eq_on_dense
-- name    : BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.eq_of_inner_eq_on_dense
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:11:12.792226+00:00
-- url     : https://prove2.me/theorems/0eda91e4-65bf-4993-ae1b-dd0b7ab008dd
-- title:
--   `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.eq_of_inner_eq_on_dense` {D : Set H} (hD : Dense D) {v w : H} (h : ∀ z ∈ D, ⟪z, v⟫_ℂ = ⟪z, w⟫_ℂ) : v = w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneConverse`.
--
--   `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.eq_of_inner_eq_on_dense` {D : Set H} (hD : Dense D) {v w : H} (h : ∀ z ∈ D, ⟪z, v⟫_ℂ = ⟪z, w⟫_ℂ) : v = w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.eq_of_inner_eq_on_dense`.

-- Generated from ChapterStoneConverse.lean — theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.eq_of_inner_eq_on_dense
import Mathlib
import Definitions.Def_ChapterStoneConverse
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable


open scoped InnerProductSpace
open Filter Topology MeasureTheory


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable (G : WeakMeasurableUnitaryGroup H)

theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.eq_of_inner_eq_on_dense {D : Set H} (hD : Dense D) {v w : H}
    (h : ∀ z ∈ D, ⟪z, v⟫_ℂ = ⟪z, w⟫_ℂ) : v = w := by sorry

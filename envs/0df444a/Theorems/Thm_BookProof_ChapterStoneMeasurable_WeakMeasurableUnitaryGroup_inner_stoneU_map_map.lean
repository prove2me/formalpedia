-- Prove2me | Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_inner_stoneU_map_map
-- name    : BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_stoneU_map_map
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:11:09.429976+00:00
-- url     : https://prove2.me/theorems/c9515709-cf1f-49c0-826e-4fceae6601b8
-- title:
--   `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_stoneU_map_map` (T : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint H) (u : ℝ) (a b : H) : ⟪T.stoneU u a, T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneConverse`.
--
--   `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_stoneU_map_map` (T : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint H) (u : ℝ) (a b : H) : ⟪T.stoneU u a, T.stoneU u b⟫_ℂ = ⟪a, b⟫_ℂ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_stoneU_map_map`.

-- Generated from ChapterStoneConverse.lean — theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_stoneU_map_map
import Mathlib
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable


open scoped InnerProductSpace
open Filter Topology MeasureTheory


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable (G : WeakMeasurableUnitaryGroup H)

theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_stoneU_map_map (T : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint H)
    (u : ℝ) (a b : H) : ⟪T.stoneU u a, T.stoneU u b⟫_ℂ = ⟪a, b⟫_ℂ := by sorry

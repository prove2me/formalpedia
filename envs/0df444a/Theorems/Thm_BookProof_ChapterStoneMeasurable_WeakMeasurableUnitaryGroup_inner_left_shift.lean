-- Prove2me | Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_inner_left_shift
-- name    : BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_left_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:11:58.362326+00:00
-- url     : https://prove2.me/theorems/6444a305-8f4c-419b-b67f-8347a62561f9
-- title:
--   `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_left_shift` (s t : ℝ) (x y : H) : ⟪ y, G.U s (G.U t x) ⟫_ℂ = ⟪ G.U (-s) y, G.U t x ⟫_ℂ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneMeasurable`.
--
--   `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_left_shift` (s t : ℝ) (x y : H) : ⟪ y, G.U s (G.U t x) ⟫_ℂ = ⟪ G.U (-s) y, G.U t x ⟫_ℂ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_left_shift`.

-- Generated from ChapterStoneMeasurable.lean — theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_left_shift
import Mathlib
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneConverse
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable


open scoped InnerProductSpace
open Filter Topology MeasureTheory


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (G : WeakMeasurableUnitaryGroup H)

theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.inner_left_shift (s t : ℝ) (x y : H) :
    ⟪ y, G.U s (G.U t x) ⟫_ℂ = ⟪ G.U (-s) y, G.U t x ⟫_ℂ := by sorry

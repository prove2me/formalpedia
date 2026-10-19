-- Prove2me | Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_gen_stoneU_eq
-- name    : BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:46:56.816515+00:00
-- url     : https://prove2.me/theorems/0e134b0b-bbb4-4a73-96fa-b7799fcd70df
-- title:
--   `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_eq` (t : ℝ) : G.gen.stoneU t = G.U t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneConverse`.
--
--   `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_eq` (t : ℝ) : G.gen.stoneU t = G.U t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_eq`.

-- Generated from ChapterStoneConverse.lean — theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_eq
import Mathlib
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneUnitary
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable


open scoped InnerProductSpace
open Filter Topology MeasureTheory


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable (G : WeakMeasurableUnitaryGroup H)

theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_eq (t : ℝ) : G.gen.stoneU t = G.U t := by sorry

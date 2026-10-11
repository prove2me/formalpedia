-- Prove2me | Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_gen_stoneU_apply_eq_domain
-- name    : BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_apply_eq_domain
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:17:28.101002+00:00
-- url     : https://prove2.me/theorems/d99ac842-c068-4a33-a007-c4758de1dd40
-- title:
--   `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_apply_eq_domain` (t : ℝ) (x : G.genDomain) : G.gen.stoneU t (x : H) = G.U t (x : H)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneConverse`.
--
--   `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_apply_eq_domain` (t : ℝ) (x : G.genDomain) : G.gen.stoneU t (x : H) = G.U t (x : H)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_apply_eq_domain`.

-- Generated from ChapterStoneConverse.lean — theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_apply_eq_domain
import Mathlib
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable


open scoped InnerProductSpace
open Filter Topology MeasureTheory


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable (G : WeakMeasurableUnitaryGroup H)

theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_apply_eq_domain (t : ℝ) (x : G.genDomain) :
    G.gen.stoneU t (x : H) = G.U t (x : H) := by sorry

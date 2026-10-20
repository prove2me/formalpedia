-- Prove2me | Theorems.Thm_BookProof_ChapterStoneSeparable_stone_exists_unique_generator
-- name    : BookProof.ChapterStoneSeparable.stone_exists_unique_generator
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T05:01:22.34519+00:00
-- url     : https://prove2.me/theorems/3f21e725-5400-4f9f-bbcb-290227b17d8e
-- title:
--   `BookProof.ChapterStoneSeparable.stone_exists_unique_generator` (G : WeakMeasurableUnitaryGroup H) : ∃! T : UnboundedSelfAdjoint H, ∀ t : ℝ, T.stoneU t = G.U t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneSeparable`.
--
--   `BookProof.ChapterStoneSeparable.stone_exists_unique_generator` (G : WeakMeasurableUnitaryGroup H) : ∃! T : UnboundedSelfAdjoint H, ∀ t : ℝ, T.stoneU t = G.U t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneSeparable.stone_exists_unique_generator`.

-- Generated from ChapterStoneSeparable.lean — theorem BookProof.ChapterStoneSeparable.stone_exists_unique_generator
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterStoneSeparable
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneTheorem
import Definitions.Def_ChapterStoneUnitary
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneTheorem
open BookProof.ChapterStoneSeparable


open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterStoneMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem BookProof.ChapterStoneSeparable.stone_exists_unique_generator (G : WeakMeasurableUnitaryGroup H) :
    ∃! T : UnboundedSelfAdjoint H, ∀ t : ℝ, T.stoneU t = G.U t := by sorry

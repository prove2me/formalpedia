-- Prove2me | Theorems.Thm_BookProof_ChapterStoneSeparable_stone_exists_unique_group
-- name    : BookProof.ChapterStoneSeparable.stone_exists_unique_group
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T05:01:35.998507+00:00
-- url     : https://prove2.me/theorems/fd349f2e-bb7f-4435-98d1-52493265bf6a
-- title:
--   `BookProof.ChapterStoneSeparable.stone_exists_unique_group` (T : UnboundedSelfAdjoint H) : ∃! G : WeakMeasurableUnitaryGroup H, ∀ x : T.domain, HasDerivAt (fun t : ℝ => G.U t (x :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneSeparable`.
--
--   `BookProof.ChapterStoneSeparable.stone_exists_unique_group` (T : UnboundedSelfAdjoint H) : ∃! G : WeakMeasurableUnitaryGroup H, ∀ x : T.domain, HasDerivAt (fun t : ℝ => G.U t (x : H)) ((-Complex.I) • T.op x) 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneSeparable.stone_exists_unique_group`.

-- Generated from ChapterStoneSeparable.lean — theorem BookProof.ChapterStoneSeparable.stone_exists_unique_group
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneConverse
import Mathlib
import Definitions.Def_ChapterStoneSeparable
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneTheorem
open BookProof.ChapterStoneTheorem
open BookProof.ChapterStoneSeparable


open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterStoneMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem BookProof.ChapterStoneSeparable.stone_exists_unique_group (T : UnboundedSelfAdjoint H) :
    ∃! G : WeakMeasurableUnitaryGroup H,
      ∀ x : T.domain, HasDerivAt (fun t : ℝ => G.U t (x : H)) ((-Complex.I) • T.op x) 0 := by sorry

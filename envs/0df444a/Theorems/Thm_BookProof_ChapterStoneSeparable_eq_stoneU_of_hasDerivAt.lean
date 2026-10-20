-- Prove2me | Theorems.Thm_BookProof_ChapterStoneSeparable_eq_stoneU_of_hasDerivAt
-- name    : BookProof.ChapterStoneSeparable.eq_stoneU_of_hasDerivAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T05:01:37.187975+00:00
-- url     : https://prove2.me/theorems/3ffb2bbf-48f7-45d7-aec7-80c4b0e22ddb
-- title:
--   `BookProof.ChapterStoneSeparable.eq_stoneU_of_hasDerivAt` (T : UnboundedSelfAdjoint H) (G : WeakMeasurableUnitaryGroup H) (h : ∀ x : T.domain, HasDerivAt (fun t : ℝ => G.U t (x : H
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneSeparable`.
--
--   `BookProof.ChapterStoneSeparable.eq_stoneU_of_hasDerivAt` (T : UnboundedSelfAdjoint H) (G : WeakMeasurableUnitaryGroup H) (h : ∀ x : T.domain, HasDerivAt (fun t : ℝ => G.U t (x : H)) ((-Complex.I) • T.op x) 0) (t : ℝ) : G.U t = T.stoneU t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneSeparable.eq_stoneU_of_hasDerivAt`.

-- Generated from ChapterStoneSeparable.lean — theorem BookProof.ChapterStoneSeparable.eq_stoneU_of_hasDerivAt
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterStoneSeparable
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneSeparable


open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterStoneMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem BookProof.ChapterStoneSeparable.eq_stoneU_of_hasDerivAt (T : UnboundedSelfAdjoint H) (G : WeakMeasurableUnitaryGroup H)
    (h : ∀ x : T.domain, HasDerivAt (fun t : ℝ => G.U t (x : H)) ((-Complex.I) • T.op x) 0)
    (t : ℝ) : G.U t = T.stoneU t := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterStoneMeasurable_WeakMeasurableUnitaryGroup_mem_genDomain_of_hasDerivAt
-- name    : BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.mem_genDomain_of_hasDerivAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:46:53.620777+00:00
-- url     : https://prove2.me/theorems/b964103b-c8c2-4fbe-8e54-4ad56387279b
-- title:
--   `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.mem_genDomain_of_hasDerivAt` {x y : H} (h : HasDerivAt (fun t : ℝ => G.U t x) y 0) : x ∈ G.genDomain
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneConverse`.
--
--   `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.mem_genDomain_of_hasDerivAt` {x y : H} (h : HasDerivAt (fun t : ℝ => G.U t x) y 0) : x ∈ G.genDomain
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.mem_genDomain_of_hasDerivAt`.

-- Generated from ChapterStoneConverse.lean — theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.mem_genDomain_of_hasDerivAt
import Mathlib
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable


open scoped InnerProductSpace
open Filter Topology MeasureTheory


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable (G : WeakMeasurableUnitaryGroup H)

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in

theorem BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.mem_genDomain_of_hasDerivAt {x y : H} (h : HasDerivAt (fun t : ℝ => G.U t x) y 0) :
    x ∈ G.genDomain := by sorry

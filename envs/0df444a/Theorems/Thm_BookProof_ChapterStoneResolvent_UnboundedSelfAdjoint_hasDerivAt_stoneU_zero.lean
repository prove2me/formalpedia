-- Prove2me | Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_hasDerivAt_stoneU_zero
-- name    : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:11:34.280533+00:00
-- url     : https://prove2.me/theorems/a9770753-a594-4406-8343-97044cdf358e
-- title:
--   `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_zero` (x : T.domain) : HasDerivAt (fun t : ℝ => T.stoneU t (x : H)) ((-Complex.I) • T.op x) 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneGenerator`.
--
--   `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_zero` (x : T.domain) : HasDerivAt (fun t : ℝ => T.stoneU t (x : H)) ((-Complex.I) • T.op x) 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_zero`.

-- Generated from ChapterStoneGenerator.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_zero
import Mathlib
import Definitions.Def_ChapterStoneGenerator
import Definitions.Def_ChapterStoneEvolution
import Definitions.Def_ChapterStoneGroup
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent


open scoped InnerProductSpace
open Filter Topology NormedSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


variable (T : UnboundedSelfAdjoint H)

theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_zero (x : T.domain) :
    HasDerivAt (fun t : ℝ => T.stoneU t (x : H)) ((-Complex.I) • T.op x) 0 := by sorry

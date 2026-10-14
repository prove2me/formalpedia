-- Prove2me | Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_hasDerivAt_stoneU
-- name    : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:11:39.936469+00:00
-- url     : https://prove2.me/theorems/93d45fe9-c363-404c-980a-7117a49efa98
-- title:
--   `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU` (x : T.domain) (t : ℝ) : HasDerivAt (fun s : ℝ => T.stoneU s (x : H)) (T.stoneU t ((-Complex.I) • T.op x))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneGenerator`.
--
--   `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU` (x : T.domain) (t : ℝ) : HasDerivAt (fun s : ℝ => T.stoneU s (x : H)) (T.stoneU t ((-Complex.I) • T.op x)) t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU`.

-- Generated from ChapterStoneGenerator.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU
import Mathlib
import Definitions.Def_ChapterStoneGenerator
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent


open scoped InnerProductSpace
open Filter Topology NormedSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


variable (T : UnboundedSelfAdjoint H)

theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU (x : T.domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => T.stoneU s (x : H)) (T.stoneU t ((-Complex.I) • T.op x)) t := by sorry

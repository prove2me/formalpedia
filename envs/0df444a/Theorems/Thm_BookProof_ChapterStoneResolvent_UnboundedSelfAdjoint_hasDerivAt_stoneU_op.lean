-- Prove2me | Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_hasDerivAt_stoneU_op
-- name    : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_op
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:11:53.038265+00:00
-- url     : https://prove2.me/theorems/b588c103-4e2f-4d77-9c59-555ecce1bf8f
-- title:
--   `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_op` (x : T.domain) (t : ℝ) : HasDerivAt (fun s : ℝ => T.stoneU s (x : H)) ((-Complex.I) • T.op ⟨T.stoneU t (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneGenerator`.
--
--   `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_op` (x : T.domain) (t : ℝ) : HasDerivAt (fun s : ℝ => T.stoneU s (x : H)) ((-Complex.I) • T.op ⟨T.stoneU t (x : H), T.stoneU_mem_domain t x⟩) t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_op`.

-- Generated from ChapterStoneGenerator.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_op
import Mathlib
import Definitions.Def_ChapterStoneGenerator
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent


open scoped InnerProductSpace
open Filter Topology NormedSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


variable (T : UnboundedSelfAdjoint H)

theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_op (x : T.domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => T.stoneU s (x : H))
      ((-Complex.I) • T.op ⟨T.stoneU t (x : H), T.stoneU_mem_domain t x⟩) t := by sorry

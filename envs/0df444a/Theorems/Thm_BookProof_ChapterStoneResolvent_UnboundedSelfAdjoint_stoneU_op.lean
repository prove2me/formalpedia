-- Prove2me | Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_stoneU_op
-- name    : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_op
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:11:44.871873+00:00
-- url     : https://prove2.me/theorems/779de379-e62d-4d75-9da9-05973b9f6085
-- title:
--   `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_op` (t : ℝ) (x : T.domain) : T.op ⟨T.stoneU t (x : H), T.stoneU_mem_domain t x⟩ = T.stoneU t (T.op x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneGenerator`.
--
--   `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_op` (t : ℝ) (x : T.domain) : T.op ⟨T.stoneU t (x : H), T.stoneU_mem_domain t x⟩ = T.stoneU t (T.op x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_op`.

-- Generated from ChapterStoneGenerator.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_op
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

theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_op (t : ℝ) (x : T.domain) :
    T.op ⟨T.stoneU t (x : H), T.stoneU_mem_domain t x⟩ = T.stoneU t (T.op x) := by sorry

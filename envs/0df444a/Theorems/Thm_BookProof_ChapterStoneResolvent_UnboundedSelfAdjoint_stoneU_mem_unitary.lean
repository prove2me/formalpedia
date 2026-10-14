-- Prove2me | Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_stoneU_mem_unitary
-- name    : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_mem_unitary
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:13:00.563236+00:00
-- url     : https://prove2.me/theorems/acf7de47-984d-4e5e-a7ed-12661f8c231d
-- title:
--   `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_mem_unitary` (t : ℝ) : T.stoneU t ∈ unitary (H →L[ℂ] H)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneUnitary`.
--
--   `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_mem_unitary` (t : ℝ) : T.stoneU t ∈ unitary (H →L[ℂ] H)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_mem_unitary`.

-- Generated from ChapterStoneUnitary.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_mem_unitary
import Mathlib
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent


open scoped InnerProductSpace
open Filter Topology NormedSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



variable (T : UnboundedSelfAdjoint H)

theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_mem_unitary (t : ℝ) : T.stoneU t ∈ unitary (H →L[ℂ] H) := by sorry

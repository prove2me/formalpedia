-- Prove2me | Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_approxU_zero_param
-- name    : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.approxU_zero_param
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T05:04:36.328129+00:00
-- url     : https://prove2.me/theorems/fc7d1041-5b33-4cfd-ab4e-c5bb2863a26d
-- title:
--   The Lean 4 theorem `approxU_zero_param` in the `ChapterStoneUnitary` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.approxU_zero_param` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterStoneUnitary.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.approxU_zero_param
import Mathlib
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterStoneEvolution
import Definitions.Def_ChapterStoneGroup
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)


open scoped InnerProductSpace
open Filter Topology NormedSpace

theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.approxU_zero_param (t : ℝ) : T.approxU 0 t = 1 := by sorry

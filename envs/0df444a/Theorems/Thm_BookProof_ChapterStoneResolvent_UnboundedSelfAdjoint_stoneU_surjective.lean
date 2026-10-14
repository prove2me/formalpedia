-- Prove2me | Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_stoneU_surjective
-- name    : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_surjective
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:12:19.962843+00:00
-- url     : https://prove2.me/theorems/bac7db3f-9172-412c-b837-76b6671a30d8
-- title:
--   `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_surjective` (t : ℝ) : Function.Surjective (T.stoneU t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneUnitary`.
--
--   `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_surjective` (t : ℝ) : Function.Surjective (T.stoneU t)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_surjective`.

-- Generated from ChapterStoneUnitary.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_surjective
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

theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_surjective (t : ℝ) : Function.Surjective (T.stoneU t) := by sorry

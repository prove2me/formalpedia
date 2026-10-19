-- Prove2me | Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_norm_resCLM_apply_le_prime
-- name    : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.norm_resCLM_apply_le_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:11:51.342981+00:00
-- url     : https://prove2.me/theorems/5f45abf7-9a07-4959-a23d-15583171c908
-- title:
--   BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.norm_resCLM_apply_le'
-- statement:
--   BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.norm_resCLM_apply_le'

-- Generated from ChapterStoneGroup.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.norm_resCLM_apply_le'
import Definitions.Def_ChapterUnitaryTransport
import Mathlib
import Definitions.Def_ChapterStoneGroup
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent


open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterUnitaryTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


variable (T : UnboundedSelfAdjoint H)

theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.norm_resCLM_apply_le_prime {n : ℝ} (y : H) :
    ‖T.resCLM (-n) y‖ ≤ (1 / |n|) * ‖y‖ := by sorry

-- Prove2me | Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_selfAdjointExtension
-- name    : BookProof.StoneBridge.exists_stone_flow_of_selfAdjointExtension
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:14:55.953592+00:00
-- url     : https://prove2.me/theorems/a3f949f3-d011-44c5-9913-f5a66f578d50
-- title:
--   The Lean 4 theorem `exists_stone_flow_of_selfAdjointExtension` in the `ChapterStoneBridge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `exists_stone_flow_of_selfAdjointExtension` in the `ChapterStoneBridge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStoneBridge.lean

-- Generated from ChapterStoneBridge.lean — theorem BookProof.StoneBridge.exists_stone_flow_of_selfAdjointExtension
import Mathlib
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkBandLedger
open BookProof.StoneBridge






open Filter Topology
open scoped InnerProductSpace


open BookProof.FarisLavine BookProof.EsaClosure BookProof.YangMillsFriedrichs
open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]










variable [CompleteSpace F]

theorem BookProof.StoneBridge.exists_stone_flow_of_selfAdjointExtension {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) :
    ∃ (T : UnboundedSelfAdjoint F) (U : ℝ → (F →L[ℂ] F)),
      T.domain = Dom ∧ HEq T.op A ∧ IsStoneFlow T U := by sorry

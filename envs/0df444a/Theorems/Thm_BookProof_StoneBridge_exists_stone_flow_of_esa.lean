-- Prove2me | Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
-- name    : BookProof.StoneBridge.exists_stone_flow_of_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:14:41.772494+00:00
-- url     : https://prove2.me/theorems/eb79005d-70bd-4864-9155-b1c03cff7b7b
-- title:
--   The Lean 4 theorem `exists_stone_flow_of_esa` in the `ChapterStoneBridge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `exists_stone_flow_of_esa` in the `ChapterStoneBridge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStoneBridge.lean

-- Generated from ChapterStoneBridge.lean — theorem BookProof.StoneBridge.exists_stone_flow_of_esa
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

theorem BookProof.StoneBridge.exists_stone_flow_of_esa {D : Submodule ℂ F} (Hc : D →ₗ[ℂ] F)
    (hdense : Dense ((D : Submodule ℂ F) : Set F)) (hsym : SymmetricOn D Hc)
    (hesa : EssentiallySelfAdjointOn D Hc) :
    ∃ (T : UnboundedSelfAdjoint F) (U : ℝ → (F →L[ℂ] F)),
      IsSelfAdjointExtension Hc T.op ∧ IsStoneFlow T U := by sorry

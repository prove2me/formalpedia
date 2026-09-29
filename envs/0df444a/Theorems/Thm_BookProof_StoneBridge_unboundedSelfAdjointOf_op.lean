-- Prove2me | Theorems.Thm_BookProof_StoneBridge_unboundedSelfAdjointOf_op
-- name    : BookProof.StoneBridge.unboundedSelfAdjointOf_op
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:18:57.925995+00:00
-- url     : https://prove2.me/theorems/c676d8a4-231a-4140-97fd-1e0f1c40108a
-- title:
--   The Lean 4 theorem `unboundedSelfAdjointOf_op` in the `ChapterStoneBridge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `unboundedSelfAdjointOf_op` in the `ChapterStoneBridge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStoneBridge.lean

-- Generated from ChapterStoneBridge.lean — theorem BookProof.StoneBridge.unboundedSelfAdjointOf_op
import Mathlib
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkBandLedger
open BookProof.StoneBridge






open Filter Topology
open scoped InnerProductSpace


open BookProof.FarisLavine BookProof.EsaClosure BookProof.YangMillsFriedrichs
open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.StoneBridge.unboundedSelfAdjointOf_op {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) :
    (unboundedSelfAdjointOf hdense h).op = A := by sorry

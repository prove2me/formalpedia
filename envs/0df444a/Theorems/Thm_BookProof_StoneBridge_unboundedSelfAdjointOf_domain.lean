-- Prove2me | Theorems.Thm_BookProof_StoneBridge_unboundedSelfAdjointOf_domain
-- name    : BookProof.StoneBridge.unboundedSelfAdjointOf_domain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:19:25.214403+00:00
-- url     : https://prove2.me/theorems/adfd5965-28d3-4737-8d68-a452d1260fb1
-- title:
--   The Lean 4 theorem `unboundedSelfAdjointOf_domain` in the `ChapterStoneBridge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `unboundedSelfAdjointOf_domain` in the `ChapterStoneBridge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStoneBridge.lean

-- Generated from ChapterStoneBridge.lean — theorem BookProof.StoneBridge.unboundedSelfAdjointOf_domain
import Mathlib
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkBandLedger
open BookProof.StoneBridge






open Filter Topology
open scoped InnerProductSpace


open BookProof.FarisLavine BookProof.EsaClosure BookProof.YangMillsFriedrichs
open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.StoneBridge.unboundedSelfAdjointOf_domain {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) :
    (unboundedSelfAdjointOf hdense h).domain = Dom := by sorry

-- Prove2me | Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_xN_mem
-- name    : Formalism.CoboundaryTransfers.WachMod.xN_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:49.570803+00:00
-- url     : https://prove2.me/theorems/15f31fb5-994d-4fdb-8143-c907c5317625
-- title:
--   Wach Mod: x N mem
-- statement:
--   The Wach Mod construction uses the x N mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/MemCoboundariesOfIsOneCoboundary.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/MemCoboundariesOfIsOneCoboundary.lean#L36-L37

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
open Formalism.CoboundaryTransfers.WachMod
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)

theorem Formalism.CoboundaryTransfers.WachMod.xN_mem {z : D} (hz : W.XN z) : z ∈ W.N := by sorry

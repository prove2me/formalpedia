-- Prove2me | Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_cocycle_mem_Zf
-- name    : Formalism.CoboundaryTransfers.WachMod.cocycle_mem_Zf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:42.608057+00:00
-- url     : https://prove2.me/theorems/97db39be-7e9c-43c8-8524-64ade0466d01
-- title:
--   Wach Mod: cocycle mem Zf
-- statement:
--   The Wach Mod construction uses the cocycle mem Zf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/MemCoboundariesOfIsOneCoboundary.lean#L193-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/MemCoboundariesOfIsOneCoboundary.lean#L193-L197

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

theorem Formalism.CoboundaryTransfers.WachMod.cocycle_mem_Zf {y z : D} (h : W.Cocycle y z) : (y, z) ∈ W.Zf := by sorry

-- Prove2me | Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_qInv_sub
-- name    : Formalism.CoboundaryTransfers.WachMod.qInv_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:55.891391+00:00
-- url     : https://prove2.me/theorems/08a39555-0187-4716-a7e2-1dfb1d3f633b
-- title:
--   Wach Mod: q Inv sub
-- statement:
--   The Wach Mod construction uses the q Inv sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/MemCoboundariesOfIsOneCoboundary.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/MemCoboundariesOfIsOneCoboundary.lean#L27-L28

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

theorem Formalism.CoboundaryTransfers.WachMod.qInv_sub {y y' : D} (hy : W.QInv y) (hy' : W.QInv y') : W.QInv (y - y') := by sorry

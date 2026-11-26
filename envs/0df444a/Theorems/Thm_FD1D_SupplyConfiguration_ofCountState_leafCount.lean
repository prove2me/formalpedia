-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_ofCountState_leafCount
-- name    : FD1D.SupplyConfiguration.ofCountState_leafCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:42:19.022999+00:00
-- url     : https://prove2.me/theorems/c1fadb42-2f2b-489a-bf2b-cc2d32cd2a3d
-- title:
--   Supply Configuration: of Count State leaf Count
-- statement:
--   The Supply Configuration construction uses the of Count State leaf Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Realization.lean#L118-L124
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Realization.lean#L118-L124

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_Realization
set_option autoImplicit true
open FD1D
noncomputable section
open Set
open FD1D.SupplyConfiguration
variable {L m : ℕ}

theorem FD1D.SupplyConfiguration.ofCountState_leafCount
    (x : InventoryState (DyadicNode L) m) (i : DyadicNode L) :
    (ofCountState x).leafCount i = x.1 i := by sorry

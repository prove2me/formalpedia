-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_ofCountState_countState
-- name    : FD1D.SupplyConfiguration.ofCountState_countState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:41:48.860537+00:00
-- url     : https://prove2.me/theorems/23db7721-2b2e-425b-80b7-d7038e2fee10
-- title:
--   Supply Configuration: of Count State count State
-- statement:
--   The canonical spatial realization projects back to the original state.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Realization.lean#L128-L133
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Realization.lean#L128-L133

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_Realization
set_option autoImplicit true
open FD1D
noncomputable section
open Set
open FD1D.SupplyConfiguration
variable {L m : ℕ}

theorem FD1D.SupplyConfiguration.ofCountState_countState
    (x : InventoryState (DyadicNode L) m) :
    (ofCountState x).countState = x := by sorry

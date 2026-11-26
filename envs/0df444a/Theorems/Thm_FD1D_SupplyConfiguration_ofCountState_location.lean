-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_ofCountState_location
-- name    : FD1D.SupplyConfiguration.ofCountState_location
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:42:00.912672+00:00
-- url     : https://prove2.me/theorems/bbd56c3b-5a55-437f-8069-b6998c605aae
-- title:
--   Supply Configuration: of Count State location
-- statement:
--   The Supply Configuration construction uses the of Count State location property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Realization.lean#L111-L115
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Realization.lean#L111-L115

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_Realization
set_option autoImplicit true
open FD1D
noncomputable section
open Set
open FD1D.SupplyConfiguration
variable {L m : ℕ}

theorem FD1D.SupplyConfiguration.ofCountState_location
    (x : InventoryState (DyadicNode L) m) (j : Fin m) :
    (ofCountState x).location j =
      dyadicCellLeft ((ofCountState x).leaf j) := by sorry

attribute [defeq] FD1D.SupplyConfiguration.ofCountState_location

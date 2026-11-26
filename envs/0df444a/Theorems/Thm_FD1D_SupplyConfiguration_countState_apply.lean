-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
-- name    : FD1D.SupplyConfiguration.countState_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:58.978309+00:00
-- url     : https://prove2.me/theorems/fda80ad4-d29c-528f-9285-ea14372bdb4d
-- title:
--   Supply Configuration: count State apply
-- statement:
--   The Supply Configuration construction uses the count State apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L436-L438
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L436-L438

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory
open FD1D.SupplyConfiguration
variable {L m : ℕ}

theorem FD1D.SupplyConfiguration.countState_apply (C : SupplyConfiguration L m) (i : DyadicNode L) :
    C.countState.1 i = C.leafCount i := by sorry

attribute [defeq] FD1D.SupplyConfiguration.countState_apply

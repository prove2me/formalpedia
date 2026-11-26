-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_representative_leaf
-- name    : FD1D.SupplyConfiguration.representative_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:52.725902+00:00
-- url     : https://prove2.me/theorems/7fd0a873-fe2a-4be1-adc5-04774d665a48
-- title:
--   Supply Configuration: representative leaf
-- statement:
--   The Supply Configuration construction uses the representative leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L449-L453
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L449-L453

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

theorem FD1D.SupplyConfiguration.representative_leaf (C : SupplyConfiguration L m) (fallback : Fin m)
    (i : DyadicNode L) (h : ∃ j, C.leaf j = i) :
    C.leaf (C.representative fallback i) = i := by sorry

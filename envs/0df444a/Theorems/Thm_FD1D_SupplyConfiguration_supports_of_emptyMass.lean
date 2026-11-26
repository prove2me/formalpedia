-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_supports_of_emptyMass
-- name    : FD1D.SupplyConfiguration.supports_of_emptyMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:35.356705+00:00
-- url     : https://prove2.me/theorems/5270a361-e69c-51dc-ba27-1fcb050e9e4d
-- title:
--   Supply Configuration: supports of empty Mass
-- statement:
--   The Supply Configuration construction uses the supports of empty Mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L459-L469
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L459-L469

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

theorem FD1D.SupplyConfiguration.supports_of_emptyMass (C : SupplyConfiguration L m)
    (q : DyadicMass L)
    (hempty : ∀ i, C.leafCount i = 0 → q.leafMass i = 0) :
    C.Supports q := by sorry

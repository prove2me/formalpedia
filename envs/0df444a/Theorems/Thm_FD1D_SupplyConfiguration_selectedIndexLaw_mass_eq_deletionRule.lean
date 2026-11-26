-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_selectedIndexLaw_mass_eq_deletionRule
-- name    : FD1D.SupplyConfiguration.selectedIndexLaw_mass_eq_deletionRule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:41:09.602423+00:00
-- url     : https://prove2.me/theorems/2aa7bb78-d9ff-48d5-aef1-b9709f3d1678
-- title:
--   Supply Configuration: selected Index Law mass eq deletion Rule
-- statement:
--   The selected leaf marginal is exactly the deletion marginal.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L693-L699
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L693-L699

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

theorem FD1D.SupplyConfiguration.selectedIndexLaw_mass_eq_deletionRule
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (R : DeletionRule (DyadicNode L) m)
    (hmass : ∀ i, q.leafMass i = R.prob C.countState i)
    (i : DyadicNode L) :
    (q.selectedIndexLaw hq).mass i = R.prob C.countState i := by sorry

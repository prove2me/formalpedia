-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_expectedActualDistance_le_one_cell_of_deletionRule
-- name    : FD1D.SupplyConfiguration.expectedActualDistance_le_one_cell_of_deletionRule
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:41:57.57629+00:00
-- url     : https://prove2.me/theorems/3c101653-3d34-4e2a-bfc4-f3f60dce5b1e
-- title:
--   Supply Configuration: expected Actual Distance le one cell of deletion Rule
-- statement:
--   Actual-point transport for a configuration realizing a deletion rule: the
--   empty-leaf condition needed for feasibility is discharged by the rule.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L723-L732
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L723-L732

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

theorem FD1D.SupplyConfiguration.expectedActualDistance_le_one_cell_of_deletionRule
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (R : DeletionRule (DyadicNode L) m)
    (hmass : ∀ i, q.leafMass i = R.prob C.countState i)
    (fallback : Fin m) :
    C.expectedActualDistance q fallback ≤
      dyadicCellWidth L +
        cdfTransportArea (fun z => q.piecewiseCDF z - z) := by sorry

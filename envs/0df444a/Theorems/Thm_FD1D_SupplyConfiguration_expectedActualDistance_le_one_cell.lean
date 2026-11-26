-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_expectedActualDistance_le_one_cell
-- name    : FD1D.SupplyConfiguration.expectedActualDistance_le_one_cell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:15:50.937704+00:00
-- url     : https://prove2.me/theorems/f9467391-d2ac-5cfe-9d1c-53f71875a39d
-- title:
--   Supply Configuration: expected Actual Distance le one cell
-- statement:
--   Selecting an actual occupied point costs at most the exact CDF quantile area
--   plus one cell width.  There is only one discretization term.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L629-L674
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L629-L674

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

theorem FD1D.SupplyConfiguration.expectedActualDistance_le_one_cell
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (hsupport : C.Supports q)
    (fallback : Fin m) :
    C.expectedActualDistance q fallback ≤
      dyadicCellWidth L +
        cdfTransportArea (fun z => q.piecewiseCDF z - z) := by sorry

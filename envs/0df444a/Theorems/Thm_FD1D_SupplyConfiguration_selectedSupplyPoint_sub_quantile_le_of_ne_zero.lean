-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_selectedSupplyPoint_sub_quantile_le_of_ne_zero
-- name    : FD1D.SupplyConfiguration.selectedSupplyPoint_sub_quantile_le_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:15:30.892267+00:00
-- url     : https://prove2.me/theorems/97381b87-a4f5-44d2-a8ce-121d5a5ecd9b
-- title:
--   Supply Configuration: selected Supply Point sub quantile le of ne zero
-- statement:
--   For every nonexceptional demand, the actual selected point and continuous
--   quantile lie in one and the same depth-`L` cell.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L554-L570
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L554-L570

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

theorem FD1D.SupplyConfiguration.selectedSupplyPoint_sub_quantile_le_of_ne_zero
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (hsupport : C.Supports q)
    (fallback : Fin m) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hu0 : u ≠ 0) :
    |C.selectedSupplyPoint q fallback u - q.quantile u| ≤
      dyadicCellWidth L := by sorry

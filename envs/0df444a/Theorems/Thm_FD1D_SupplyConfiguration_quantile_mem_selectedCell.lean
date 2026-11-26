-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_quantile_mem_selectedCell
-- name    : FD1D.SupplyConfiguration.quantile_mem_selectedCell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:15:19.279932+00:00
-- url     : https://prove2.me/theorems/a954873e-b492-43f4-953a-184b2b3cc8ad
-- title:
--   Supply Configuration: quantile mem selected Cell
-- statement:
--   The continuous quantile belongs to the cell indexed by `selectedIndex`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L531-L548
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L531-L548

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

theorem FD1D.SupplyConfiguration.quantile_mem_selectedCell
    (q : DyadicMass L) (hq : q.IsProbability)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    q.quantile u ∈ dyadicCell (q.selectedIndex u) := by sorry

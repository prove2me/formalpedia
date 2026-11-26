-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_selectedSupplyIndex_leaf_of_ne_zero
-- name    : FD1D.SupplyConfiguration.selectedSupplyIndex_leaf_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:38.239668+00:00
-- url     : https://prove2.me/theorems/a2f2f46e-7fd8-4e63-85c9-f8416fff70dc
-- title:
--   Supply Configuration: selected Supply Index leaf of ne zero
-- statement:
--   Except at the zero demand boundary, the total representative really carries
--   the recursively selected leaf label.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L498-L512
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L498-L512

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

theorem FD1D.SupplyConfiguration.selectedSupplyIndex_leaf_of_ne_zero
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (hsupport : C.Supports q)
    (fallback : Fin m) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hu0 : u ≠ 0) :
    C.leaf (C.selectedSupplyIndex q fallback u) = q.selectedIndex u := by sorry

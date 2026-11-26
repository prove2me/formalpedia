-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_selectedSupplyIndex_leaf_ae
-- name    : FD1D.SupplyConfiguration.selectedSupplyIndex_leaf_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:40:21.674321+00:00
-- url     : https://prove2.me/theorems/9f092c3f-63b7-5874-ae12-43fcf3168819
-- title:
--   Supply Configuration: selected Supply Index leaf ae
-- statement:
--   The selected configured item is feasible for almost every uniform demand.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L515-L528
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L515-L528

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

theorem FD1D.SupplyConfiguration.selectedSupplyIndex_leaf_ae
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (hsupport : C.Supports q)
    (fallback : Fin m) :
    ∀ᵐ u ∂DyadicMass.uniformDemand,
      C.leaf (C.selectedSupplyIndex q fallback u) = q.selectedIndex u := by sorry

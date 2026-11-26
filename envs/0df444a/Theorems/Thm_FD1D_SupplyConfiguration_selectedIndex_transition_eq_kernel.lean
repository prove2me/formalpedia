-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_selectedIndex_transition_eq_kernel
-- name    : FD1D.SupplyConfiguration.selectedIndex_transition_eq_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:41:07.46315+00:00
-- url     : https://prove2.me/theorems/23fae82a-e701-4a2a-b0e8-16ea3211e7ee
-- title:
--   Supply Configuration: selected Index transition eq kernel
-- statement:
--   After an independent uniform arrival leaf, the concrete selected-leaf
--   marginal produces exactly the count transition kernel.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L705-L717
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L705-L717

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

theorem FD1D.SupplyConfiguration.selectedIndex_transition_eq_kernel
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (R : DeletionRule (DyadicNode L) m)
    (hmass : ∀ i, q.leafMass i = R.prob C.countState i)
    (y : InventoryState (DyadicNode L) m) :
    (∑ deleted, ∑ arrived,
      if InventoryState.move C.countState deleted arrived = y then
        (q.selectedIndexLaw hq).mass deleted *
          (1 / Fintype.card (DyadicNode L) : ℝ)
      else 0) =
      R.kernel C.countState y := by sorry

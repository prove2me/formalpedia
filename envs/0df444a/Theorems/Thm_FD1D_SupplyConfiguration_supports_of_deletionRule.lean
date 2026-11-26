-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_supports_of_deletionRule
-- name    : FD1D.SupplyConfiguration.supports_of_deletionRule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:13.029805+00:00
-- url     : https://prove2.me/theorems/a4e03c4a-ce35-4509-82e7-678ca95ab507
-- title:
--   Supply Configuration: supports of deletion Rule
-- statement:
--   If the dyadic leaf masses are a deletion rule's probabilities at the count
--   projection, support by occupied concrete leaves follows automatically.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L682-L690
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L682-L690

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

theorem FD1D.SupplyConfiguration.supports_of_deletionRule
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (R : DeletionRule (DyadicNode L) m)
    (hmass : ∀ i, q.leafMass i = R.prob C.countState i) :
    C.Supports q := by sorry

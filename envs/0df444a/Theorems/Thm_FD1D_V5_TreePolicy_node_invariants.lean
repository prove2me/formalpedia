-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_node_invariants
-- name    : FD1D.V5.TreePolicy.node_invariants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:35:44.145841+00:00
-- url     : https://prove2.me/theorems/29659633-ac80-5830-a071-77ad8363ee4b
-- title:
--   Tree Policy: node invariants
-- statement:
--   The Tree Policy construction uses the node invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L215-L297
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L215-L297

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.node_invariants
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    ∀ d, d ≤ L → ∀ v,
      0 < rate I a d v ∧
        discrepancy I a d v ≤ rate I a d v / 2 ∧
        regularizedMass I a d v ≤ rate I a d v := by sorry

-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_local_bellman_inequality
-- name    : FD1D.V5.TreePolicy.local_bellman_inequality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:56:31.595498+00:00
-- url     : https://prove2.me/theorems/9349a867-c88e-4b95-bd4a-459016a3df37
-- title:
--   Tree Policy: local bellman inequality
-- statement:
--   The Tree Policy construction uses the local bellman inequality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L457-L536
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L457-L536

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_LocalBellman_local_bellman_inequality

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.local_bellman_inequality
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    childAverage
          (fun d v => discrepancy I a d v *
            regularizedMass I a d v) d v +
        childAverage (bellmanValue I a) d v -
        bellmanValue I a d v ≥
      (childAverage (fun d v => rate I a d v ^ 2) d v -
          rate I a d v ^ 2 +
          imbalance I a d v ^ 2 / a ^ 2) / 1000 := by sorry

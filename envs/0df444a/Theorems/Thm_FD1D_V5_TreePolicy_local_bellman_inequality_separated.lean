-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_local_bellman_inequality_separated
-- name    : FD1D.V5.TreePolicy.local_bellman_inequality_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:37:49.048799+00:00
-- url     : https://prove2.me/theorems/d54ab5c1-3249-565b-82e9-c409e92f37cd
-- title:
--   Tree Policy: local bellman inequality separated
-- statement:
--   The local certificate with its two energy terms separated.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L539-L560
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L539-L560

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.local_bellman_inequality_separated
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    childAverage
          (fun d v => discrepancy I a d v *
            regularizedMass I a d v) d v +
        childAverage (bellmanValue I a) d v -
        bellmanValue I a d v ≥
      (childAverage (fun d v => rate I a d v ^ 2) d v -
          rate I a d v ^ 2) / 1000 +
        imbalance I a d v ^ 2 / (1000 * a ^ 2) := by sorry

-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_local_rate_average_ge
-- name    : FD1D.V5.TreePolicy.local_rate_average_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:37:44.727039+00:00
-- url     : https://prove2.me/theorems/bc75bc37-f3b1-458f-9702-54525d026ed7
-- title:
--   Tree Policy: local rate average ge
-- statement:
--   The Tree Policy construction uses the local rate average ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L381-L395
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L381-L395

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.local_rate_average_ge
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    rate I a d v ≤
      childAverage (rate I a) d v := by sorry

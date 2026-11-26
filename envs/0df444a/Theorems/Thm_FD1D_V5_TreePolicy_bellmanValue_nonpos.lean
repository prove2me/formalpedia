-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_bellmanValue_nonpos
-- name    : FD1D.V5.TreePolicy.bellmanValue_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:37:18.365041+00:00
-- url     : https://prove2.me/theorems/52df7a1e-9927-568c-94aa-f48c7ab79e83
-- title:
--   Tree Policy: bellman Value nonpos
-- statement:
--   The Tree Policy construction uses the bellman Value nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L370-L377
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L370-L377

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.bellmanValue_nonpos
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    bellmanValue I a d v ≤ 0 := by sorry

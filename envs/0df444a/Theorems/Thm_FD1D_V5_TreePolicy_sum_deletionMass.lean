-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_sum_deletionMass
-- name    : FD1D.V5.TreePolicy.sum_deletionMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:37.239979+00:00
-- url     : https://prove2.me/theorems/69e437a8-8d38-4f63-b529-185c75bb5f00
-- title:
--   Tree Policy: sum deletion Mass
-- statement:
--   The Tree Policy construction uses the sum deletion Mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L338-L347
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L338-L347

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.sum_deletionMass (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) :
    ∑ v, deletionMass I a d v = 1 := by sorry

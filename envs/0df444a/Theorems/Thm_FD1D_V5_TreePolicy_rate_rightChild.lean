-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_rate_rightChild
-- name    : FD1D.V5.TreePolicy.rate_rightChild
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:35:04.107806+00:00
-- url     : https://prove2.me/theorems/d7d38393-d5dc-5226-bae6-1264d99da134
-- title:
--   Tree Policy: rate right Child
-- statement:
--   The Tree Policy construction uses the rate right Child property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L80-L87
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L80-L87

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.rate_rightChild (I : AggregatedInventory L m) (a : ℝ)
    (d : ℕ) (v : DyadicNode d) :
    rate I a (d + 1) (rightChild v) =
      rateRight a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by sorry

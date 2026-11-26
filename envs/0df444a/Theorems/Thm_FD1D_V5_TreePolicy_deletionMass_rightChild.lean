-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_deletionMass_rightChild
-- name    : FD1D.V5.TreePolicy.deletionMass_rightChild
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:35:53.467269+00:00
-- url     : https://prove2.me/theorems/aa981e21-0c9e-4353-9b0e-a6ce6b0870cd
-- title:
--   Tree Policy: deletion Mass right Child
-- statement:
--   The Tree Policy construction uses the deletion Mass right Child property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L118-L125
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L118-L125

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.deletionMass_rightChild (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    deletionMass I a (d + 1) (rightChild v) =
      massRight a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by sorry

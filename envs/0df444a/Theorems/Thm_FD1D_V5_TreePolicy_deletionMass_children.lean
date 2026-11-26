-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_deletionMass_children
-- name    : FD1D.V5.TreePolicy.deletionMass_children
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:37:33.425242+00:00
-- url     : https://prove2.me/theorems/b3665d32-4f99-4409-8a6c-0843efefb4f8
-- title:
--   Tree Policy: deletion Mass children
-- statement:
--   The Tree Policy construction uses the deletion Mass children property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L127-L136
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L127-L136

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.deletionMass_children (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    deletionMass I a d v =
      deletionMass I a (d + 1) (leftChild v) +
        deletionMass I a (d + 1) (rightChild v) := by sorry

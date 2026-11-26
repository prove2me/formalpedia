-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_deletionMass_leftChild
-- name    : FD1D.V5.TreePolicy.deletionMass_leftChild
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:35:38.374637+00:00
-- url     : https://prove2.me/theorems/d2f34026-d376-490d-8874-764511a9057a
-- title:
--   Tree Policy: deletion Mass left Child
-- statement:
--   The Tree Policy construction uses the deletion Mass left Child property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L109-L116
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L109-L116

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.deletionMass_leftChild (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    deletionMass I a (d + 1) (leftChild v) =
      massLeft a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by sorry

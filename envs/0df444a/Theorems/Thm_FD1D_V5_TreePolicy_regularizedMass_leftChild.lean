-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_regularizedMass_leftChild
-- name    : FD1D.V5.TreePolicy.regularizedMass_leftChild
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:36:20.50859+00:00
-- url     : https://prove2.me/theorems/279c944a-0ef5-55d7-ad79-727079be8860
-- title:
--   Tree Policy: regularized Mass left Child
-- statement:
--   The Tree Policy construction uses the regularized Mass left Child property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L197-L203
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L197-L203

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.regularizedMass_leftChild (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    regularizedMass I a (d + 1) (leftChild v) =
      regularizedMassLeft a (intervalMass d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by sorry

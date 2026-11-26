-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_rightChild
-- name    : FD1D.V5.TreePolicy.discrepancy_rightChild
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:36:35.129213+00:00
-- url     : https://prove2.me/theorems/9ed71b2c-a692-4a1e-8fc1-f02e12ed7a6f
-- title:
--   Tree Policy: discrepancy right Child
-- statement:
--   The Tree Policy construction uses the discrepancy right Child property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L188-L195
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L188-L195

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.discrepancy_rightChild (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    discrepancy I a (d + 1) (rightChild v) =
      discrepancyRight a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by sorry

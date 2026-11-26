-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_leftChild
-- name    : FD1D.V5.TreePolicy.discrepancy_leftChild
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:36:47.173694+00:00
-- url     : https://prove2.me/theorems/9715251c-9f22-4842-ab75-413aec521cd4
-- title:
--   Tree Policy: discrepancy left Child
-- statement:
--   The Tree Policy construction uses the discrepancy left Child property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L179-L186
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L179-L186

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.discrepancy_leftChild (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    discrepancy I a (d + 1) (leftChild v) =
      discrepancyLeft a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by sorry

-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_regularizedMass_eq_local
-- name    : FD1D.V5.TreePolicy.regularizedMass_eq_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:36:51.03721+00:00
-- url     : https://prove2.me/theorems/16185f38-786a-572c-955a-09cb9ed706d8
-- title:
--   Tree Policy: regularized Mass eq local
-- statement:
--   The Tree Policy construction uses the regularized Mass eq local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L170-L177
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L170-L177

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.regularizedMass_eq_local (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    regularizedMass I a d v =
      LocalPolicy.regularizedMass a (intervalMass d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by sorry

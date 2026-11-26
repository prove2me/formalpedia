-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_leftChild
-- name    : FD1D.V5.TreePolicy.intervalMass_leftChild
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:35:43.506002+00:00
-- url     : https://prove2.me/theorems/8259d2df-03d7-4806-98ad-84db818eb5bd
-- title:
--   Tree Policy: interval Mass left Child
-- statement:
--   The Tree Policy construction uses the interval Mass left Child property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L93-L95
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L93-L95

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.intervalMass_leftChild (d : ℕ) (v : DyadicNode d) :
    intervalMass (d + 1) (leftChild v) = intervalMass d v / 2 := by sorry

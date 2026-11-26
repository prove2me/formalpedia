-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_rightChild
-- name    : FD1D.V5.TreePolicy.intervalMass_rightChild
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:35:08.448689+00:00
-- url     : https://prove2.me/theorems/4f279f2a-b2e1-5d24-a171-8a137e720d61
-- title:
--   Tree Policy: interval Mass right Child
-- statement:
--   The Tree Policy construction uses the interval Mass right Child property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L97-L99
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L97-L99

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.intervalMass_rightChild (d : ℕ) (v : DyadicNode d) :
    intervalMass (d + 1) (rightChild v) = intervalMass d v / 2 := by sorry

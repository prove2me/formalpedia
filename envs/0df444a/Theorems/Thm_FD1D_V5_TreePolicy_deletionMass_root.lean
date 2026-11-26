-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_deletionMass_root
-- name    : FD1D.V5.TreePolicy.deletionMass_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:36:26.443185+00:00
-- url     : https://prove2.me/theorems/799db1ab-5398-4cd2-8a11-485c9af33266
-- title:
--   Tree Policy: deletion Mass root
-- statement:
--   The Tree Policy construction uses the deletion Mass root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L138-L141
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L138-L141

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.deletionMass_root (I : AggregatedInventory L m) (a : ℝ)
    (hm : 0 < m) :
    deletionMass I a 0 dyadicRoot = 1 := by sorry

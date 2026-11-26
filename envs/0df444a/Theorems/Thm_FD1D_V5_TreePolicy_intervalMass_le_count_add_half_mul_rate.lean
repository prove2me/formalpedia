-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_le_count_add_half_mul_rate
-- name    : FD1D.V5.TreePolicy.intervalMass_le_count_add_half_mul_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:01.396084+00:00
-- url     : https://prove2.me/theorems/59f38609-7c76-5b5b-b87d-270853cbc732
-- title:
--   Tree Policy: interval Mass le count add half mul rate
-- statement:
--   The Tree Policy construction uses the interval Mass le count add half mul rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L318-L329
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L318-L329

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.intervalMass_le_count_add_half_mul_rate
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    intervalMass d v ≤
      (inventory I d v + a / 2) * rate I a d v := by sorry

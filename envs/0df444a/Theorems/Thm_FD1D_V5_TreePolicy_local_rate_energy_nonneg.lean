-- Prove2me | Theorems.Thm_FD1D_V5_TreePolicy_local_rate_energy_nonneg
-- name    : FD1D.V5.TreePolicy.local_rate_energy_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:37:27.256779+00:00
-- url     : https://prove2.me/theorems/7243a044-caf8-4159-99a8-12029c68db79
-- title:
--   Tree Policy: local rate energy nonneg
-- statement:
--   The Tree Policy construction uses the local rate energy nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L397-L421
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean#L397-L421

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}

theorem FD1D.V5.TreePolicy.local_rate_energy_nonneg
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    0 ≤ childAverage (fun d v => rate I a d v ^ 2) d v -
      rate I a d v ^ 2 := by sorry

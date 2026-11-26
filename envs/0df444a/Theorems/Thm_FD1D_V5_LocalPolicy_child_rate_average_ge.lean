-- Prove2me | Theorems.Thm_FD1D_V5_LocalPolicy_child_rate_average_ge
-- name    : FD1D.V5.LocalPolicy.child_rate_average_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:22:23.688796+00:00
-- url     : https://prove2.me/theorems/1c268af5-d1d6-4fbd-a693-cbf98d061e81
-- title:
--   Local Policy: child rate average ge
-- statement:
--   The Local Policy construction uses the child rate average ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L448-L464
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L448-L464

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section

theorem FD1D.V5.LocalPolicy.child_rate_average_ge
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (ht : discrepancy a p h x y ≤ h / 2) :
    h ≤ (rateLeft a p h x y + rateRight a p h x y) / 2 := by sorry

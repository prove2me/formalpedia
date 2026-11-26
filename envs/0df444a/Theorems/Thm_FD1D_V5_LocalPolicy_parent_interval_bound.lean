-- Prove2me | Theorems.Thm_FD1D_V5_LocalPolicy_parent_interval_bound
-- name    : FD1D.V5.LocalPolicy.parent_interval_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:09.107152+00:00
-- url     : https://prove2.me/theorems/542724b0-655b-5e06-aac3-7b87f48c37db
-- title:
--   Local Policy: parent interval bound
-- statement:
--   The Local Policy construction uses the parent interval bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L29-L39
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L29-L39

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section

theorem FD1D.V5.LocalPolicy.parent_interval_bound
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a)
    (ht : discrepancy a p h x y ≤ h / 2) :
    p ≤ h * (inventory x y + a / 2) := by sorry

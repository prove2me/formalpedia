-- Prove2me | Theorems.Thm_FD1D_V5_LocalPolicy_discrepancy_le_half_iff_regularizedMass_le
-- name    : FD1D.V5.LocalPolicy.discrepancy_le_half_iff_regularizedMass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:49.904973+00:00
-- url     : https://prove2.me/theorems/ef06534a-d250-46a8-b320-ec18e657d663
-- title:
--   Local Policy: discrepancy le half iff regularized Mass le
-- statement:
--   The Local Policy construction uses the discrepancy le half iff regularized Mass le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L11-L27
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L11-L27

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section

theorem FD1D.V5.LocalPolicy.discrepancy_le_half_iff_regularizedMass_le
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a) :
    discrepancy a p h x y ≤ h / 2 ↔
      regularizedMass a p x y ≤ h := by sorry

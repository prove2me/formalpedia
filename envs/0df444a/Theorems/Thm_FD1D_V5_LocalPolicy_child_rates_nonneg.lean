-- Prove2me | Theorems.Thm_FD1D_V5_LocalPolicy_child_rates_nonneg
-- name    : FD1D.V5.LocalPolicy.child_rates_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:22:34.944842+00:00
-- url     : https://prove2.me/theorems/65f900e8-8bec-4257-a48d-7ae59b729866
-- title:
--   Local Policy: child rates nonneg
-- statement:
--   The Local Policy construction uses the child rates nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L348-L360
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L348-L360

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section

theorem FD1D.V5.LocalPolicy.child_rates_nonneg
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (ht : discrepancy a p h x y ≤ h / 2) :
    0 ≤ rateLeft a p h x y ∧ 0 ≤ rateRight a p h x y := by sorry

-- Prove2me | Theorems.Thm_FD1D_V5_LocalPolicy_orderedBias_nonneg
-- name    : FD1D.V5.LocalPolicy.orderedBias_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:56.5724+00:00
-- url     : https://prove2.me/theorems/1cba61fb-c22c-4533-885f-09af317087e3
-- title:
--   Local Policy: ordered Bias nonneg
-- statement:
--   The Local Policy construction uses the ordered Bias nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L88-L107
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L88-L107

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section

theorem FD1D.V5.LocalPolicy.orderedBias_nonneg
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hxy : y ≤ x)
    (ht : discrepancy a p h x y ≤ h / 2) :
    0 ≤ orderedBias a p h x y := by sorry

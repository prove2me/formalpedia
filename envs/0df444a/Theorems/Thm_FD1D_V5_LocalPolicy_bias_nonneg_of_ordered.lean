-- Prove2me | Theorems.Thm_FD1D_V5_LocalPolicy_bias_nonneg_of_ordered
-- name    : FD1D.V5.LocalPolicy.bias_nonneg_of_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:22:02.264685+00:00
-- url     : https://prove2.me/theorems/96f4ec02-dac9-4b2d-b65d-5dc140e6951e
-- title:
--   Local Policy: bias nonneg of ordered
-- statement:
--   The Local Policy construction uses the bias nonneg of ordered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L109-L115
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L109-L115

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section

theorem FD1D.V5.LocalPolicy.bias_nonneg_of_ordered
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hxy : y ≤ x)
    (ht : discrepancy a p h x y ≤ h / 2) :
    0 ≤ bias a p h x y := by sorry

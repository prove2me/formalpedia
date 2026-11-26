-- Prove2me | Theorems.Thm_FD1D_V5_LocalBellman_Normalized_lambda_lt_one
-- name    : FD1D.V5.LocalBellman.Normalized.lambda_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:26:41.824096+00:00
-- url     : https://prove2.me/theorems/bebf78a3-2379-4648-8523-c721da1a5420
-- title:
--   Normalized: lambda lt one
-- statement:
--   The Normalized construction uses the lambda lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L71-L74
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L71-L74

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized

theorem FD1D.V5.LocalBellman.Normalized.lambda_lt_one {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    lambda ρ < 1 := by sorry

-- Prove2me | Theorems.Thm_FD1D_V5_LocalBellman_Normalized_lambda_nonneg
-- name    : FD1D.V5.LocalBellman.Normalized.lambda_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:26:08.3848+00:00
-- url     : https://prove2.me/theorems/985131a8-cb77-5873-81cd-d52a61881b80
-- title:
--   Normalized: lambda nonneg
-- statement:
--   The Normalized construction uses the lambda nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L67-L69
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L67-L69

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized

theorem FD1D.V5.LocalBellman.Normalized.lambda_nonneg (ρ : ℝ) :
    0 ≤ lambda ρ := by sorry

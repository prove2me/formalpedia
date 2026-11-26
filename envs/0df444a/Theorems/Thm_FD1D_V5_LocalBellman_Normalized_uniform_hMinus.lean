-- Prove2me | Theorems.Thm_FD1D_V5_LocalBellman_Normalized_uniform_hMinus
-- name    : FD1D.V5.LocalBellman.Normalized.uniform_hMinus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:26:31.402919+00:00
-- url     : https://prove2.me/theorems/e8fb214d-e094-5948-afa1-5d4930d1c679
-- title:
--   Normalized: uniform h Minus
-- statement:
--   The Normalized construction uses the uniform h Minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L146-L151
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L146-L151

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized

theorem FD1D.V5.LocalBellman.Normalized.uniform_hMinus {s ρ : ℝ}
    (hs : 0 < s) (hρ1 : ρ ≠ 1) :
    hMinus s ρ (uniform s ρ) = 1 := by sorry

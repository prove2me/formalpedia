-- Prove2me | Theorems.Thm_FD1D_V5_LocalBellman_Normalized_equal_case
-- name    : FD1D.V5.LocalBellman.Normalized.equal_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:27:07.71542+00:00
-- url     : https://prove2.me/theorems/22db9bb3-eaa7-43f3-908e-8c437777c584
-- title:
--   Normalized: equal case
-- statement:
--   The Normalized construction uses the equal case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L1397-L1426
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L1397-L1426

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized

theorem FD1D.V5.LocalBellman.Normalized.equal_case
    {s r : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2) :
    residual s r 0 0 ≥
      (rateIncrement s 0 0 + 0 ^ 2) / 1000 := by sorry

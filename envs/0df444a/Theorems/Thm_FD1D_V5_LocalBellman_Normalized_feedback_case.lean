-- Prove2me | Theorems.Thm_FD1D_V5_LocalBellman_Normalized_feedback_case
-- name    : FD1D.V5.LocalBellman.Normalized.feedback_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:28:07.808244+00:00
-- url     : https://prove2.me/theorems/93a57141-37e7-4220-b87c-8cc9dac1b5e4
-- title:
--   Normalized: feedback case
-- statement:
--   The Normalized construction uses the feedback case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L610-L746
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L610-L746

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
set_option maxHeartbeats 800000

theorem FD1D.V5.LocalBellman.Normalized.feedback_case
    {s r ρ : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hactive : feedback s ρ ≤ uniform s ρ) :
    residual s r ρ (feedback s ρ) ≥
      (rateIncrement s ρ (feedback s ρ) + feedback s ρ ^ 2) / 1000 := by sorry

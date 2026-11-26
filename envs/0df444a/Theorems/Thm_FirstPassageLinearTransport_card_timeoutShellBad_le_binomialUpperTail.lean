-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_timeoutShellBad_le_binomialUpperTail
-- name    : FirstPassageLinearTransport.card_timeoutShellBad_le_binomialUpperTail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:41:04.085048+00:00
-- url     : https://prove2.me/theorems/34526bc6-ff00-517e-b4ec-6821418e4ad4
-- title:
--   First Passage Linear Transport: card timeout Shell Bad le binomial Upper Tail
-- statement:
--   Exact finite timeout count before asymptotic rate comparison.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L900-L913
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L900-L913

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.card_timeoutShellBad_le_binomialUpperTail
    {K₀ : ℝ} {L m : ℕ}
    (hk : timeoutOddThreshold (timeoutTargetRank K₀ L m) ≤ m) :
    (timeoutShellBad K₀ L m).card ≤
      binomialUpperTail m
        (timeoutOddThreshold (timeoutTargetRank K₀ L m)) := by sorry

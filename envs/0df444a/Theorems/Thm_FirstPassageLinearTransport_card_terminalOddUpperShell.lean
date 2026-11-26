-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_terminalOddUpperShell
-- name    : FirstPassageLinearTransport.card_terminalOddUpperShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:35.154249+00:00
-- url     : https://prove2.me/theorems/700418e9-819a-41c0-ad85-06b2ad885b08
-- title:
--   First Passage Linear Transport: card terminal Odd Upper Shell
-- statement:
--   Exact binomial law for the terminal odd count on a complete dyadic
--   shell.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L459-L478
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L459-L478

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.card_terminalOddUpperShell {m k : ℕ} (hk : k ≤ m) :
    (terminalOddUpperShell m k).card = binomialUpperTail m k := by sorry

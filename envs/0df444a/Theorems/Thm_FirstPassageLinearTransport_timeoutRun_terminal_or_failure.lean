-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutRun_terminal_or_failure
-- name    : FirstPassageLinearTransport.timeoutRun_terminal_or_failure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:43:25.646254+00:00
-- url     : https://prove2.me/theorems/fb5d287c-2c7d-4ae6-85c0-d632c772d2bd
-- title:
--   First Passage Linear Transport: timeout Run terminal or failure
-- statement:
--   A started timeout run either produces a terminal iterate or places its
--   original source in the separated failure envelope.  The induction is on the
--   strictly decreasing reached threshold rank.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutExecution.lean#L61-L169
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutExecution.lean#L61-L169

import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
import Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.timeoutRun_terminal_or_failure
    (P : TimeoutHighRunData) (K₀ : ℝ)
    {L M S n elapsed q : ℕ}
    (hL2 : 2 ≤ L) (_hLS : L ≤ S)
    (hHiStartup : P.pHi.M0 ≤ L)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextParent : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p - 1)
    (hqM : q ≤ M - 1)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    HasTimeoutTerminalLanding P K₀ L M S n ∨
      n ∈ timeoutSeparatedFailureEnvelope P K₀ M L S := by sorry

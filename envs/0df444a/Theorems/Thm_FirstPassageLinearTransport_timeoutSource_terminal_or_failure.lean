-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutSource_terminal_or_failure
-- name    : FirstPassageLinearTransport.timeoutSource_terminal_or_failure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:26:49.731659+00:00
-- url     : https://prove2.me/theorems/5d9b5a7d-2719-4003-afa3-34ed6b0eb0b9
-- title:
--   First Passage Linear Transport: timeout Source terminal or failure
-- statement:
--   Every source in the outer shell either reaches the timeout terminal target
--   or belongs to the literal separated failure envelope.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutExecution.lean#L173-L203
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutExecution.lean#L173-L203

import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
import Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.timeoutSource_terminal_or_failure
    (P : TimeoutHighRunData) (K₀ : ℝ)
    {M L S n : ℕ}
    (hSM : S ≤ M) (hM0 : P.pHi.M0 ≤ M)
    (hL2 : 2 ≤ L) (hLS : L ≤ S)
    (hHiStartup : P.pHi.M0 ≤ L)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextParent : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p - 1)
    (hq0M : rationalTargetRank P.rHi M ≤ M - 1)
    (hnShell : n ∈ dyadicShell M) :
    HasTimeoutTerminalLanding P K₀ L M S n ∨
      n ∈ timeoutSeparatedFailureEnvelope P K₀ M L S := by sorry

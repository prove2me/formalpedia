-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_sqrtSupport_mul_terminalTail_polylog_le_power
-- name    : FirstPassageLinearTransport.eventually_sqrtSupport_mul_terminalTail_polylog_le_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:44:24.567788+00:00
-- url     : https://prove2.me/theorems/8afa53fe-c819-474b-a9a3-87a7e9fa749a
-- title:
--   First Passage Linear Transport: eventually sqrt Support mul terminal Tail polylog le power
-- statement:
--   The terminal profile multiplied by the compressed feasible-time support
--   loses exactly one half power of the shell rank.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTailAsymptotics.lean#L70-L104
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTailAsymptotics.lean#L70-L104

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_sqrtSupport_mul_terminalTail_polylog_le_power
    {A b b' c' kappa : ℝ}
    (hA : 0 < A)
    (hb' : 0 < b') (hbb' : b' < b)
    (hc' : 0 < c') (hc2 : c' < Real.log 2)
    (hkappa : kappa < A * min b' c' / Real.log 2 - 1 / 2) :
    ∀ᶠ M : ℕ in atTop,
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
          terminalTailBound b b' c' (polylogTerminalRank A M) ≤
        terminalTailPrefactor b b' c' *
          (((M : ℝ) + 2) ^ (-kappa)) := by sorry

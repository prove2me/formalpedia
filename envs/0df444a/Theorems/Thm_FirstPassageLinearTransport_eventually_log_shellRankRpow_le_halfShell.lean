-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_log_shellRankRpow_le_halfShell
-- name    : FirstPassageLinearTransport.eventually_log_shellRankRpow_le_halfShell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:56:16.1784+00:00
-- url     : https://prove2.me/theorems/ef24f127-77c1-48cc-a839-e4f65782d0e4
-- title:
--   First Passage Linear Transport: eventually log shell Rank Rpow le half Shell
-- statement:
--   Every fixed power of the shell rank satisfies the logarithmic-slope
--   hypothesis of the reciprocal maximum theorem at the half-shell prefix.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedJointExceptionalOrder.lean#L145-L209
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedJointExceptionalOrder.lean#L145-L209

import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_log_shellRankRpow_le_halfShell
    {q : ℝ} (hq : 0 ≤ q) :
    ∀ᶠ M : ℕ in atTop,
      Real.log (((M : ℝ) + 2) ^ q) ≤
        reciprocalMaximumEpsilon * ((M / 2 : ℕ) : ℝ) * Real.log 3 := by sorry

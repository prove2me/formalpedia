-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_fixedJointPolylogTarget_lt_halfShell
-- name    : FirstPassageLinearTransport.eventually_fixedJointPolylogTarget_lt_halfShell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:56:07.710894+00:00
-- url     : https://prove2.me/theorems/8fdffb23-462d-4399-8493-884d5644a2e1
-- title:
--   First Passage Linear Transport: eventually fixed Joint Polylog Target lt half Shell
-- statement:
--   A fixed polylogarithmic target cannot be reached in the first half of a
--   large shell solely by repeated halvings.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedJointExceptionalOrder.lean#L54-L136
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedJointExceptionalOrder.lean#L54-L136

import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_fixedJointPolylogTarget_lt_halfShell
    {C A : ℝ} (hC : 0 < C) (hA : 0 ≤ A) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ, n ∈ dyadicShell M →
      fixedJointPolylogTarget C A n <
        (n : ℝ) / (2 : ℝ) ^ (M / 2) := by sorry

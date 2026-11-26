-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_fixedJointPolylogHeight_eq_on_shell
-- name    : FirstPassageLinearTransport.fixedJointPolylogHeight_eq_on_shell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:41.657066+00:00
-- url     : https://prove2.me/theorems/e0278dd2-ebbc-4f94-a0bd-926a707d4c02
-- title:
--   First Passage Linear Transport: fixed Joint Polylog Height eq on shell
-- statement:
--   The First Passage Linear Transport construction uses the fixed Joint Polylog Height eq on shell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedJointExceptionalOrder.lean#L138-L141
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedJointExceptionalOrder.lean#L138-L141

import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.fixedJointPolylogHeight_eq_on_shell
    (q : ℝ) {M n : ℕ} (hn : n ∈ dyadicShell M) :
    fixedJointPolylogHeight q n = ((M : ℝ) + 2) ^ q := by sorry

-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_fixedJointPolylogHeightFailureCount_ge_log_order
-- name    : FirstPassageLinearTransport.eventually_fixedJointPolylogHeightFailureCount_ge_log_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:35:39.660908+00:00
-- url     : https://prove2.me/theorems/4c46e18c-3b02-43ff-b624-10025247649b
-- title:
--   First Passage Linear Transport: eventually fixed Joint Polylog Height Failure Count ge log order
-- statement:
--   Height-forced lower half of the fixed-polylogarithmic balanced joint
--   exceptional order.  It is a target-and-height lower bound, not a lower bound
--   for target-only failure.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedJointExceptionalOrder.lean#L348-L396
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedJointExceptionalOrder.lean#L348-L396

import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_fixedJointPolylogHeightFailureCount_ge_log_order
    {C A q : ℝ} (hC : 0 < C) (hA : 0 ≤ A) (hq : 0 < q) :
    ∀ᶠ X : ℕ in atTop,
      (1 / (12 * (2 / Real.log 2) ^ q)) * (X : ℝ) *
          (Real.log X) ^ (-q) ≤
        variableTargetHeightFailureCount
          (fixedJointPolylogTarget C A) (fixedJointPolylogHeight q) X := by sorry

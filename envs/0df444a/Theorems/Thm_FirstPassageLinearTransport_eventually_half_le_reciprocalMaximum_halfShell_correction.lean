-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_half_le_reciprocalMaximum_halfShell_correction
-- name    : FirstPassageLinearTransport.eventually_half_le_reciprocalMaximum_halfShell_correction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:56:20.082528+00:00
-- url     : https://prove2.me/theorems/8f8854e9-01be-4494-819d-ae7ff67820e4
-- title:
--   First Passage Linear Transport: eventually half le reciprocal Maximum half Shell correction
-- statement:
--   The finite reciprocal correction is eventually at least one half on the
--   half-shell prefix.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedJointExceptionalOrder.lean#L213-L239
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedJointExceptionalOrder.lean#L213-L239

import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_half_le_reciprocalMaximum_halfShell_correction :
    ∀ᶠ M : ℕ in atTop,
      (1 / 2 : ℝ) ≤
        1 - reciprocalMaximumConstant / ((M / 2 : ℕ) : ℝ) := by sorry

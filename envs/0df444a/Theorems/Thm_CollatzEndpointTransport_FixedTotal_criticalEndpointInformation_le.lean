-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_criticalEndpointInformation_le
-- name    : CollatzEndpointTransport.FixedTotal.criticalEndpointInformation_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:57:19.245574+00:00
-- url     : https://prove2.me/theorems/967f1ba8-802c-480f-85b5-26a1bbd5aea0
-- title:
--   Fixed Total: critical Endpoint Information le
-- statement:
--   **Global critical endpoint-information theorem.**
--
--   The `M^(3/2)` polynomial is a conservative formal mixture loss.  It is
--   sufficient for the optimized nonlinear pullback because the exponential
--   rate remains unchanged.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalGlobalEndpointMoment.lean#L311-L346
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalGlobalEndpointMoment.lean#L311-L346

import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.globalCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.criticalEndpointInformation_le
    (M : ℕ) (hM : 1 ≤ M) :
    criticalEndpointInformation M ≤
      9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M := by sorry

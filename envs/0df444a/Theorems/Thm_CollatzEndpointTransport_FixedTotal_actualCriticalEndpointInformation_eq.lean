-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualCriticalEndpointInformation_eq
-- name    : CollatzEndpointTransport.FixedTotal.actualCriticalEndpointInformation_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:00:04.409146+00:00
-- url     : https://prove2.me/theorems/767c94fc-670c-559f-8ac7-1c5dae73aa85
-- title:
--   Fixed Total: actual Critical Endpoint Information eq
-- statement:
--   The literal shell endpoint information is exactly the decomposed finite
--   quantity bounded in `FixedTotalGlobalEndpointMoment`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalActualEndpointMoment.lean#L169-L207
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalActualEndpointMoment.lean#L169-L207

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.actualCriticalEndpointInformation_eq
    (M : ℕ) :
    actualCriticalEndpointInformation M =
      criticalEndpointInformation M := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralEndpointInformation_le
-- name    : CollatzEndpointTransport.FixedTotal.centralEndpointInformation_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:03:34.467112+00:00
-- url     : https://prove2.me/theorems/dcc33917-3a65-4036-9c70-85c8befa0ba1
-- title:
--   Fixed Total: central Endpoint Information le
-- statement:
--   Polynomial central endpoint-information bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L416-L626
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L416-L626

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralShellCompositionDecidableEq
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralRenyiAdmissibleDecidable

theorem CollatzEndpointTransport.FixedTotal.centralEndpointInformation_le
    {M : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    centralEndpointInformation M theta eta ≤
      (3 : ℝ) ^ theta * centralMomentConstant theta eta *
        (M + 1 : ℝ) ^ 6 := by sorry

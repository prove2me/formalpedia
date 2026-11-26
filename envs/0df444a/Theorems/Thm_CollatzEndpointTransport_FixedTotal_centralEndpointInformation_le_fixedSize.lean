-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralEndpointInformation_le_fixedSize
-- name    : CollatzEndpointTransport.FixedTotal.centralEndpointInformation_le_fixedSize
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:23:33.056933+00:00
-- url     : https://prove2.me/theorems/c4797ed8-979f-5654-ad76-d99d9211eda0
-- title:
--   Fixed Total: central Endpoint Information le fixed Size
-- statement:
--   Refined central endpoint information in literal shell coordinates.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralEndpointInformation.lean#L166-L270
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralEndpointInformation.lean#L166-L270

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralAggregate
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 600000

theorem CollatzEndpointTransport.FixedTotal.centralEndpointInformation_le_fixedSize
    {M : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    centralEndpointInformation M theta eta ≤
      2 * (3 : ℝ) ^ theta *
        (fixedSizeCentralMomentConstant theta eta *
          fractionalBinomialMassConstant theta) *
        (M + 1 : ℝ) ^ (theta / 2) := by sorry

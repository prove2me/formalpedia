-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_refinedCentralRenyiMomentInverse_le
-- name    : CollatzEndpointTransport.FixedTotal.refinedCentralRenyiMomentInverse_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:24:20.651134+00:00
-- url     : https://prove2.me/theorems/04394e9b-2348-53ba-97e4-c19e88900eac
-- title:
--   Fixed Total: refined Central Renyi Moment Inverse le
-- statement:
--   Real-power conversion from the absorbed shell rate to the corresponding
--   inverse power of the input density exponent.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L79-L126
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L79-L126

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.refinedCentralRenyiMomentInverse_le
    {theta transport D : ℝ}
    (htheta : 0 < theta)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hD0 : 0 < D)
    (hlinear : transport * D ≤
      centralRenyiShellRate theta transport D / Real.log 2) :
    (((1 - centralRenyiAbsorption theta transport) *
        centralRenyiRate theta D / holderScaleExponent theta) ^
          (-holderScaleExponent theta)) ≤
      refinedCentralRenyiInverseRateFactor theta transport *
        (D⁻¹) ^ holderScaleExponent theta := by sorry

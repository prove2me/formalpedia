-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_quantitativeArbitraryTargetEndpointTransportRefined
-- name    : CollatzEndpointTransport.FixedTotal.quantitativeArbitraryTargetEndpointTransportRefined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:26:48.552498+00:00
-- url     : https://prove2.me/theorems/0f3cd992-41dc-4909-a6e7-7c8d8fd77400
-- title:
--   Fixed Total: quantitative Arbitrary Target Endpoint Transport Refined
-- statement:
--   Refined one-block arbitrary-target endpoint transport.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L552-L670
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L552-L670

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.quantitativeArbitraryTargetEndpointTransportRefined
    {theta eta transport : ℝ}
    (htheta0 : 1 / 2 < theta)
    (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    ∃ Dcut K : ℝ,
      0 < Dcut ∧ Dcut ≤ 1 ∧ 0 < K ∧
      ∀ {S : Set ℕ} {C D : ℝ},
        QuantitativeDensity.IsCDDense S C D →
        D ≤ Dcut →
        QuantitativeDensity.IsCDDense
          (QuantitativeDensity.collatzPullback S)
          (K * (1 + C ^ holderTargetExponent theta) *
            (D⁻¹) ^ holderScaleExponent theta)
          (transport * D) := by sorry

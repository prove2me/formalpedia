-- Prove2me | Theorems.Thm_CollatzEndpointTransportPalomar_quantitative_arbitrary_target_endpoint_transport
-- name    : CollatzEndpointTransportPalomar.quantitative_arbitrary_target_endpoint_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:53:51.744575+00:00
-- url     : https://prove2.me/theorems/086dc541-4390-48b8-ad2c-d1b67db7e46a
-- title:
--   Collatz Endpoint Transport Palomar: quantitative arbitrary target endpoint transport
-- statement:
--   The Collatz Endpoint Transport Palomar construction uses the quantitative arbitrary target endpoint transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/Solution.lean#L47-L86
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/Solution.lean#L47-L86

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
import Definitions.Def_CollatzEndpointTransport_Solution
set_option autoImplicit false
open CollatzEndpointTransportPalomar
open scoped Real
noncomputable section

theorem CollatzEndpointTransportPalomar.quantitative_arbitrary_target_endpoint_transport
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
        IsCDDense S C D →
        D ≤ Dcut →
        IsCDDense
          (endpointPullback S)
          (K * (1 + C ^ holderTargetExponent theta) *
            (D⁻¹) ^ holderScaleExponent theta)
          (transport * D) := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_refined_absorbed
-- name    : CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_refined_absorbed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:26:14.203252+00:00
-- url     : https://prove2.me/theorems/85d5a7de-b588-400c-952b-f64aeb25a6e5
-- title:
--   Fixed Total: source Endpoint Bad div pow le refined absorbed
-- statement:
--   Uniform refined source estimate on every dyadic shell.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L457-L549
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L457-L549

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_refined_absorbed
    {S : Set ℕ} {C D theta eta transport : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hlinear : transport * D ≤
      centralRenyiShellRate theta transport D / Real.log 2)
    (hcutLate : centralRenyiShellRate theta transport D ≤
      eta * Real.log 2 / 16)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8)
    (M : ℕ) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      refinedCentralRenyiShellConstant theta eta transport *
        (1 + C ^ holderTargetExponent theta) *
        (D⁻¹) ^ holderScaleExponent theta *
        Real.exp (-centralRenyiShellRate theta transport D * M) := by sorry

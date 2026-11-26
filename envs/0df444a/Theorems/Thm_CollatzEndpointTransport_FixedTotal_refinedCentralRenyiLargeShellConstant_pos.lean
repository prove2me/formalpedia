-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_refinedCentralRenyiLargeShellConstant_pos
-- name    : CollatzEndpointTransport.FixedTotal.refinedCentralRenyiLargeShellConstant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:13:55.385813+00:00
-- url     : https://prove2.me/theorems/625e6e02-f6dd-4d64-9e4c-316c2260ea35
-- title:
--   Fixed Total: refined Central Renyi Large Shell Constant pos
-- statement:
--   The Fixed Total construction uses the refined Central Renyi Large Shell Constant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L237-L251
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L237-L251

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.refinedCentralRenyiLargeShellConstant_pos
    {theta eta transport : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    0 < refinedCentralRenyiLargeShellConstant theta eta transport := by sorry

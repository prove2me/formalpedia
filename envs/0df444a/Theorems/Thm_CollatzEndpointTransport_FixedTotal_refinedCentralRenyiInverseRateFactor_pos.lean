-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_refinedCentralRenyiInverseRateFactor_pos
-- name    : CollatzEndpointTransport.FixedTotal.refinedCentralRenyiInverseRateFactor_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:22.698596+00:00
-- url     : https://prove2.me/theorems/d8f9b609-a5a7-445e-ae60-336b5eda3bcd
-- title:
--   Fixed Total: refined Central Renyi Inverse Rate Factor pos
-- statement:
--   The Fixed Total construction uses the refined Central Renyi Inverse Rate Factor pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L62-L75
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L62-L75

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.refinedCentralRenyiInverseRateFactor_pos
    {theta transport : ℝ}
    (htheta : 0 < theta)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    0 < refinedCentralRenyiInverseRateFactor theta transport := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_holderScaleExponent_pos
-- name    : CollatzEndpointTransport.FixedTotal.holderScaleExponent_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:53.768808+00:00
-- url     : https://prove2.me/theorems/684ea48e-08aa-5b7d-a6a8-cd9586cc3afe
-- title:
--   Fixed Total: holder Scale Exponent pos
-- statement:
--   The Fixed Total construction uses the holder Scale Exponent pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L47-L51
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L47-L51

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.holderScaleExponent_pos
    {theta : ℝ} (htheta : 0 < theta) :
    0 < holderScaleExponent theta := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_holderCentralMomentConstant_pos
-- name    : CollatzEndpointTransport.FixedTotal.holderCentralMomentConstant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:13:26.093798+00:00
-- url     : https://prove2.me/theorems/517f5b9f-a74e-45e4-8517-4c06ac8f69eb
-- title:
--   Fixed Total: holder Central Moment Constant pos
-- statement:
--   The Fixed Total construction uses the holder Central Moment Constant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralRenyiMomentTransport.lean#L33-L45
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralRenyiMomentTransport.lean#L33-L45

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiShellTransport
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.holderCentralMomentConstant_pos
    {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    0 < holderCentralMomentConstant theta eta := by sorry

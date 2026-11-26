-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiStageConstant_pos
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiStageConstant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:42:46.598907+00:00
-- url     : https://prove2.me/theorems/e25174b6-93ee-5b8e-94b5-61a34d94e93f
-- title:
--   Fixed Total: central Renyi Stage Constant pos
-- statement:
--   The Fixed Total construction uses the central Renyi Stage Constant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1832-L1850
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1832-L1850

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq

theorem CollatzEndpointTransport.FixedTotal.centralRenyiStageConstant_pos
    {theta eta transport : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    0 < centralRenyiStageConstant theta eta transport := by sorry

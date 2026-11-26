-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_lt_one
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiAbsorption_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:07:23.542004+00:00
-- url     : https://prove2.me/theorems/43f6171f-301f-462b-a61c-5b5a926d3eb2
-- title:
--   Fixed Total: central Renyi Absorption lt one
-- statement:
--   The Fixed Total construction uses the central Renyi Absorption lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L641-L649
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L641-L649

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiAbsorption_lt_one
    {theta transport : ℝ}
    (htheta : 0 < theta)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    centralRenyiAbsorption theta transport < 1 := by sorry

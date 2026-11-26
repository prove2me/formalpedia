-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_transport_lt_absorption_mul_centralRenyiAsymptoticRate
-- name    : CollatzEndpointTransport.FixedTotal.transport_lt_absorption_mul_centralRenyiAsymptoticRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:16:44.700369+00:00
-- url     : https://prove2.me/theorems/f11c1ba8-9a9d-4268-a9f3-3ec4ebd696b3
-- title:
--   Fixed Total: transport lt absorption mul central Renyi Asymptotic Rate
-- statement:
--   The Fixed Total construction uses the transport lt absorption mul central Renyi Asymptotic Rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L651-L666
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L651-L666

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

theorem CollatzEndpointTransport.FixedTotal.transport_lt_absorption_mul_centralRenyiAsymptoticRate
    {theta transport : ℝ}
    (htheta : 0 < theta)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    transport < centralRenyiAbsorption theta transport *
      centralRenyiAsymptoticRate theta := by sorry

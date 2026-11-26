-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_tendsto_centralRenyiShellRate_zero_right
-- name    : CollatzEndpointTransport.FixedTotal.tendsto_centralRenyiShellRate_zero_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:09.640127+00:00
-- url     : https://prove2.me/theorems/97c5c1a9-6e9a-51cf-bf39-3fdc837cd4b0
-- title:
--   Fixed Total: tendsto central Renyi Shell Rate zero right
-- statement:
--   The Fixed Total construction uses the tendsto central Renyi Shell Rate zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L682-L702
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L682-L702

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

theorem CollatzEndpointTransport.FixedTotal.tendsto_centralRenyiShellRate_zero_right
    (theta transport : ℝ) :
    Filter.Tendsto (centralRenyiShellRate theta transport)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by sorry

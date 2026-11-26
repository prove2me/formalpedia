-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_tendsto_centralRenyiNormalizedRate_zero_right
-- name    : CollatzEndpointTransport.FixedTotal.tendsto_centralRenyiNormalizedRate_zero_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:16:47.405153+00:00
-- url     : https://prove2.me/theorems/d34500f1-492e-5e29-8a4a-fb84641c0b14
-- title:
--   Fixed Total: tendsto central Renyi Normalized Rate zero right
-- statement:
--   The balanced central shell rate is asymptotically linear in the target
--   density exponent.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L595-L607
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L595-L607

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

theorem CollatzEndpointTransport.FixedTotal.tendsto_centralRenyiNormalizedRate_zero_right (theta : ℝ) :
    Filter.Tendsto (centralRenyiNormalizedRate theta)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (centralRenyiAsymptoticRate theta)) := by sorry

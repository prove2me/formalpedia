-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_pos
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiAbsorption_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:05:29.574803+00:00
-- url     : https://prove2.me/theorems/c4c20631-37ed-509e-a17c-b8c944964b1a
-- title:
--   Fixed Total: central Renyi Absorption pos
-- statement:
--   The Fixed Total construction uses the central Renyi Absorption pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L632-L639
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L632-L639

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiAbsorption_pos
    {theta transport : ℝ}
    (htheta : 0 < theta) (htransport : 0 < transport) :
    0 < centralRenyiAbsorption theta transport := by sorry

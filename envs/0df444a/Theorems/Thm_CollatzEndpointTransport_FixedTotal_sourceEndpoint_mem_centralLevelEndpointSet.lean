-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_mem_centralLevelEndpointSet
-- name    : CollatzEndpointTransport.FixedTotal.sourceEndpoint_mem_centralLevelEndpointSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:52.699932+00:00
-- url     : https://prove2.me/theorems/3fdd5444-95fc-504a-9f35-7373137399db
-- title:
--   Fixed Total: source Endpoint mem central Level Endpoint Set
-- statement:
--   The Fixed Total construction uses the source Endpoint mem central Level Endpoint Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L169-L180
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L169-L180

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

theorem CollatzEndpointTransport.FixedTotal.sourceEndpoint_mem_centralLevelEndpointSet
    {M s : ℕ} {theta eta : ℝ} {x : SourceCode M}
    (hx : x ∈ centralLevelSourceSet M s theta eta) :
    sourceEndpoint x ∈ centralLevelEndpointSet M s theta eta := by sorry

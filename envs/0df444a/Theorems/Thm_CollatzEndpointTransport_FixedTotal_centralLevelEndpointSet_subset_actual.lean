-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelEndpointSet_subset_actual
-- name    : CollatzEndpointTransport.FixedTotal.centralLevelEndpointSet_subset_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:16:08.182543+00:00
-- url     : https://prove2.me/theorems/ef5ec587-cab4-5ae9-a028-120c87aa8dc0
-- title:
--   Fixed Total: central Level Endpoint Set subset actual
-- statement:
--   The Fixed Total construction uses the central Level Endpoint Set subset actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L234-L249
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L234-L249

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

theorem CollatzEndpointTransport.FixedTotal.centralLevelEndpointSet_subset_actual
    (M s : ℕ) (theta eta : ℝ) :
    centralLevelEndpointSet M s theta eta ⊆
      actualLevelEndpointSet M s := by sorry

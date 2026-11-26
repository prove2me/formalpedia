-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_centralSourceEndpointBad_eq_sum
-- name    : CollatzEndpointTransport.FixedTotal.card_centralSourceEndpointBad_eq_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:08:52.830971+00:00
-- url     : https://prove2.me/theorems/149b1ef9-abce-4629-ac01-9d4cff1ee5ca
-- title:
--   Fixed Total: card central Source Endpoint Bad eq sum
-- statement:
--   Exact odd-count decomposition of the retained central bad source.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L413-L452
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L413-L452

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

theorem CollatzEndpointTransport.FixedTotal.card_centralSourceEndpointBad_eq_sum
    (S : Set ℕ) (M : ℕ) (theta eta : ℝ) :
    (centralSourceEndpointBad S M theta eta).card =
      ∑ s ∈ Finset.range (M + 1),
        centralLevelBadMass S M s theta eta := by sorry

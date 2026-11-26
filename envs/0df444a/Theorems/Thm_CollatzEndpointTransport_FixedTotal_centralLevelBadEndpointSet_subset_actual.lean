-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelBadEndpointSet_subset_actual
-- name    : CollatzEndpointTransport.FixedTotal.centralLevelBadEndpointSet_subset_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:16:04.68412+00:00
-- url     : https://prove2.me/theorems/9393c5b8-9316-53e1-ba39-ae88f1317538
-- title:
--   Fixed Total: central Level Bad Endpoint Set subset actual
-- statement:
--   The Fixed Total construction uses the central Level Bad Endpoint Set subset actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L251-L259
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L251-L259

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

theorem CollatzEndpointTransport.FixedTotal.centralLevelBadEndpointSet_subset_actual
    (S : Set ℕ) (M s : ℕ) (theta eta : ℝ) :
    centralLevelBadEndpointSet S M s theta eta ⊆
      actualLevelBadEndpointSet S M s := by sorry

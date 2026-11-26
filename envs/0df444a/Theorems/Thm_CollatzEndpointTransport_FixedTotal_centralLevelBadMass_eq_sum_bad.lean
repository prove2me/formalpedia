-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelBadMass_eq_sum_bad
-- name    : CollatzEndpointTransport.FixedTotal.centralLevelBadMass_eq_sum_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:07:12.21808+00:00
-- url     : https://prove2.me/theorems/520c8f9e-2944-5229-bf93-2a005dc35d1d
-- title:
--   Fixed Total: central Level Bad Mass eq sum bad
-- statement:
--   The Fixed Total construction uses the central Level Bad Mass eq sum bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L182-L223
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L182-L223

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

theorem CollatzEndpointTransport.FixedTotal.centralLevelBadMass_eq_sum_bad
    (S : Set ℕ) (M s : ℕ) (theta eta : ℝ) :
    centralLevelBadMass S M s theta eta =
      ∑ y ∈ centralLevelBadEndpointSet S M s theta eta,
        centralLevelFiberCard M s theta eta y := by sorry

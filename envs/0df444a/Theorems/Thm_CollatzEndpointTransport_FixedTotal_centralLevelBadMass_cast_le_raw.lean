-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelBadMass_cast_le_raw
-- name    : CollatzEndpointTransport.FixedTotal.centralLevelBadMass_cast_le_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:16:16.77215+00:00
-- url     : https://prove2.me/theorems/71c65956-3bf9-4082-98d7-178d33a299b0
-- title:
--   Fixed Total: central Level Bad Mass cast le raw
-- statement:
--   Raw one-level higher-Renyi heavy/ordinary split.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L279-L340
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L279-L340

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

theorem CollatzEndpointTransport.FixedTotal.centralLevelBadMass_cast_le_raw
    (S : Set ℕ) (M s : ℕ) (theta eta Q : ℝ)
    (hQ : 0 < Q) (htheta : 0 < theta) (hs : s ≤ M) :
    (centralLevelBadMass S M s theta eta : ℝ) ≤
      Q * ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (centralLevelBadEndpointSet S M s theta eta).card +
        Q ^ (-theta) *
          (((3 : ℝ) ^ (s + 1)) /
            (sourceOddLevel M s).card) ^ theta *
          (∑ y ∈ centralLevelEndpointSet M s theta eta,
            (centralLevelFiberCard M s theta eta y : ℝ) ^
              (1 + theta)) := by sorry

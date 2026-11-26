-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelBadMass_cast_le
-- name    : CollatzEndpointTransport.FixedTotal.centralLevelBadMass_cast_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:16:37.643941+00:00
-- url     : https://prove2.me/theorems/ab72a00b-c75e-540e-b459-01bd61e0cb84
-- title:
--   Fixed Total: central Level Bad Mass cast le
-- statement:
--   One central odd-count level after inserting the target density.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L353-L410
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L353-L410

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

theorem CollatzEndpointTransport.FixedTotal.centralLevelBadMass_cast_le
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M s : ℕ) (theta eta Q : ℝ)
    (hQ : 0 < Q) (htheta : 0 < theta) (hs : s ≤ M) :
    (centralLevelBadMass S M s theta eta : ℝ) ≤
      C * Q * (sourceOddLevel M s).card *
          (Real.exp (-D * Real.log 3)) ^ (s + 1) +
        Q ^ (-theta) * centralLevelRenyiInformation M s theta eta := by sorry

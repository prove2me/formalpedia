-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyi_lateDiscardRatio_eq
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyi_lateDiscardRatio_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:19:42.131588+00:00
-- url     : https://prove2.me/theorems/937d18e7-83d0-4a52-b335-b93e20563fa3
-- title:
--   Fixed Total: central Renyi late Discard Ratio eq
-- statement:
--   Exact real form of the late-first-odd discard ratio.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L910-L920
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L910-L920

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyi_lateDiscardRatio_eq
    {M K : ℕ} (hKM : K ≤ M) :
    ((((M + 1) * 2 ^ (M - K) : ℕ) : ℝ) / (2 ^ M : ℝ)) =
      (M + 1 : ℝ) * Real.exp (-(Real.log 2) * K) := by sorry

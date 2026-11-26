-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyi_lateDiscardRatio_le
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyi_lateDiscardRatio_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:09:35.132565+00:00
-- url     : https://prove2.me/theorems/570d2c89-ff40-5770-90db-a9d6f0f057b7
-- title:
--   Fixed Total: central Renyi late Discard Ratio le
-- statement:
--   Exponential estimate for the late-first-odd discard under the canonical
--   central cutoff.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L924-L961
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L924-L961

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyi_lateDiscardRatio_le
    (eta : ℝ) (M : ℕ)
    (hKM : centralRenyiDiscardDepth eta M ≤ M) :
    (((((M + 1) *
        2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
        (2 ^ M : ℝ))) ≤
      2 * (M + 1 : ℝ) *
        Real.exp (-(eta * Real.log 2 / 8) * M) := by sorry

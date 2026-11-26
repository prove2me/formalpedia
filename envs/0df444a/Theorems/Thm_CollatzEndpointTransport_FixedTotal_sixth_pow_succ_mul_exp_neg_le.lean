-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sixth_pow_succ_mul_exp_neg_le
-- name    : CollatzEndpointTransport.FixedTotal.sixth_pow_succ_mul_exp_neg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:44.19387+00:00
-- url     : https://prove2.me/theorems/dc0a96af-a67e-4f65-8476-e380e9fd4773
-- title:
--   Fixed Total: sixth pow succ mul exp neg le
-- statement:
--   Sixth-degree polynomial absorption used for the central moment
--   prefactor.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L965-L1010
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L965-L1010

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

theorem CollatzEndpointTransport.FixedTotal.sixth_pow_succ_mul_exp_neg_le
    {r zeta x : ℝ}
    (hr : 0 < r) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hx : 1 ≤ x) :
    (x + 1) ^ 6 * Real.exp (-r * x) ≤
      64 * ((((1 - zeta) * r / 6)⁻¹) ^ 6) *
        Real.exp (-(zeta * r) * x) := by sorry

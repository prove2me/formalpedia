-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_succ_mul_exp_neg_le
-- name    : CollatzEndpointTransport.FixedTotal.succ_mul_exp_neg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:50.919811+00:00
-- url     : https://prove2.me/theorems/ce3d954d-c1a1-459f-abcb-67402f759f41
-- title:
--   Fixed Total: succ mul exp neg le
-- statement:
--   First-degree polynomial absorption used for the late-first-odd
--   discard.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1014-L1049
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1014-L1049

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

theorem CollatzEndpointTransport.FixedTotal.succ_mul_exp_neg_le
    {r zeta x : ℝ}
    (hr : 0 < r) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hx : 1 ≤ x) :
    (x + 1) * Real.exp (-r * x) ≤
      2 * (((1 - zeta) * r)⁻¹) *
        Real.exp (-(zeta * r) * x) := by sorry

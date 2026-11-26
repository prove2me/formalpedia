-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_rpow_succ_mul_exp_neg_le
-- name    : CollatzEndpointTransport.FixedTotal.rpow_succ_mul_exp_neg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:52.587452+00:00
-- url     : https://prove2.me/theorems/a9f288c0-4736-44d6-8502-dba0e2d0706b
-- title:
--   Fixed Total: rpow succ mul exp neg le
-- statement:
--   Real-power polynomial absorption, corresponding to paper equation
--   (5.21).
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L918-L971
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L918-L971

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.rpow_succ_mul_exp_neg_le
    {B r zeta x : ℝ}
    (hB : 0 < B) (hr : 0 < r)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hx : 1 ≤ x) :
    (x + 1) ^ B * Real.exp (-r * x) ≤
      (2 : ℝ) ^ B * (((1 - zeta) * r / B) ^ (-B)) *
        Real.exp (-(zeta * r) * x) := by sorry

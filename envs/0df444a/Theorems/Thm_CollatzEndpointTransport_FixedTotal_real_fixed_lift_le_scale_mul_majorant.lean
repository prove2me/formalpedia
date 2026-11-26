-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_real_fixed_lift_le_scale_mul_majorant
-- name    : CollatzEndpointTransport.FixedTotal.real_fixed_lift_le_scale_mul_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:20.41992+00:00
-- url     : https://prove2.me/theorems/3ef3c4fa-31f4-4ca8-8d5a-aa1ee1b057e2
-- title:
--   Fixed Total: real fixed lift le scale mul majorant
-- statement:
--   Unnormalized pointwise lift bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1043-L1053
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1043-L1053

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.real_fixed_lift_le_scale_mul_majorant
    {N s : ℕ} {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (c : Composition N) (hc : c ∈ fixedSet N s) :
    (((3 ^ s + syracuseNumerator c : ℕ) : ℝ) ^ theta) ≤
      (((2 : ℝ) ^ N) ^ theta) * realReverseMajorant theta c := by sorry

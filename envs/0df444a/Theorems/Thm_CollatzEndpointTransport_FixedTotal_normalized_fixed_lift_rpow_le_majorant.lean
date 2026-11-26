-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalized_fixed_lift_rpow_le_majorant
-- name    : CollatzEndpointTransport.FixedTotal.normalized_fixed_lift_rpow_le_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:35.618844+00:00
-- url     : https://prove2.me/theorems/fec4c78b-e5b9-4275-b99f-ba7f219fc7a7
-- title:
--   Fixed Total: normalized fixed lift rpow le majorant
-- statement:
--   Composition form, tied to the forward Syracuse numerator.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L252-L261
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L252-L261

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
open Finset
open scoped NNReal
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.normalized_fixed_lift_rpow_le_majorant
    {N : ℕ} (c : Composition N) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    ((((3 ^ c.length + syracuseNumerator c : ℕ) : ℝ≥0) /
          ((2 : ℝ≥0) ^ N)) ^ theta) ≤
      reverseMomentMajorant theta c.blocks.reverse := by sorry

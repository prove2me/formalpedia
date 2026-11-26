-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_real_normalized_fixed_lift_le_majorant
-- name    : CollatzEndpointTransport.FixedTotal.real_normalized_fixed_lift_le_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:14.391896+00:00
-- url     : https://prove2.me/theorems/58542299-1cf7-4404-aa69-497cc2951313
-- title:
--   Fixed Total: real normalized fixed lift le majorant
-- statement:
--   Real form of the pointwise normalized reverse-spend majorization.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1025-L1040
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1025-L1040

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

theorem CollatzEndpointTransport.FixedTotal.real_normalized_fixed_lift_le_majorant
    {N s : ℕ} {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (c : Composition N) (hc : c ∈ fixedSet N s) :
    (((((3 ^ s + syracuseNumerator c : ℕ) : ℝ) /
          (2 : ℝ) ^ N)) ^ theta) ≤
      realReverseMajorant theta c := by sorry

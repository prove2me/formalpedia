-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_rpow_le_majorant
-- name    : CollatzEndpointTransport.FixedTotal.normalizedReverseLift_rpow_le_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:30.463125+00:00
-- url     : https://prove2.me/theorems/bcde0d1d-b337-5cd8-93de-fe94a355c737
-- title:
--   Fixed Total: normalized Reverse Lift rpow le majorant
-- statement:
--   Pointwise reverse-spend majorization.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L224-L249
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L224-L249

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

theorem CollatzEndpointTransport.FixedTotal.normalizedReverseLift_rpow_le_majorant
    {theta : ℝ} (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    ∀ ks : List ℕ,
      (normalizedReverseLift ks) ^ theta ≤
        reverseMomentMajorant theta ks := by sorry

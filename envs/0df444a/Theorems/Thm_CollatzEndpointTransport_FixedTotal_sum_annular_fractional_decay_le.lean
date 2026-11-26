-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_annular_fractional_decay_le
-- name    : CollatzEndpointTransport.FixedTotal.sum_annular_fractional_decay_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:50:35.079922+00:00
-- url     : https://prove2.me/theorems/cc6f226d-922e-597a-a565-b2088b249c8b
-- title:
--   Fixed Total: sum annular fractional decay le
-- statement:
--   The finite Gaussian annular profile is bounded by its geometric majorant.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMassBound.lean#L192-L225
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMassBound.lean#L192-L225

import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000

theorem CollatzEndpointTransport.FixedTotal.sum_annular_fractional_decay_le
    (H : ℕ) {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (∑ j ∈ Finset.range (H + 1),
        (2 * Real.exp (-2 * (j : ℝ) ^ 2)) ^ (1 - theta)) ≤
      (2 : ℝ) ^ (1 - theta) *
        (1 - Real.exp (-2 * (1 - theta)))⁻¹ := by sorry

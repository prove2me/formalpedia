-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fractional_symmetricBinomialMass_le
-- name    : CollatzEndpointTransport.FixedTotal.sum_fractional_symmetricBinomialMass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:19:22.454503+00:00
-- url     : https://prove2.me/theorems/ab366d80-7e79-4a45-89a7-1a0aed84223f
-- title:
--   Fixed Total: sum fractional symmetric Binomial Mass le
-- statement:
--   Fractional masses of the symmetric binomial law have square-root order.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMassBound.lean#L228-L268
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMassBound.lean#L228-L268

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

theorem CollatzEndpointTransport.FixedTotal.sum_fractional_symmetricBinomialMass_le
    {H : ℕ} {theta : ℝ}
    (hH : 0 < H) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (∑ k ∈ Finset.range (H + 1),
        (symmetricBinomialMass H k) ^ (1 - theta)) ≤
      fractionalBinomialMassConstant theta *
        (H + 1 : ℝ) ^ (theta / 2) := by sorry

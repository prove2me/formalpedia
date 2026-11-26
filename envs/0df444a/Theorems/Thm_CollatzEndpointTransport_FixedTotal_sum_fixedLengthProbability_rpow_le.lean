-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fixedLengthProbability_rpow_le
-- name    : CollatzEndpointTransport.FixedTotal.sum_fixedLengthProbability_rpow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:23:39.957208+00:00
-- url     : https://prove2.me/theorems/5e5c7ab5-7986-4c85-8c8c-7fa0f32fe8b8
-- title:
--   Fixed Total: sum fixed Length Probability rpow le
-- statement:
--   Fractional masses of all possible composition lengths have square-root
--   order.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralAggregate.lean#L49-L85
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralAggregate.lean#L49-L85

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralAggregate
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000

theorem CollatzEndpointTransport.FixedTotal.sum_fixedLengthProbability_rpow_le
    {N : ℕ} {theta : ℝ}
    (hN : 1 < N) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (∑ s ∈ Finset.Icc 1 N,
        (fixedLengthProbability N s) ^ (1 - theta)) ≤
      fractionalBinomialMassConstant theta *
        (N : ℝ) ^ (theta / 2) := by sorry

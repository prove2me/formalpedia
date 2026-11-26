-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fixedSourceWeight_rpow_central_le
-- name    : CollatzEndpointTransport.FixedTotal.sum_fixedSourceWeight_rpow_central_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:12:44.338121+00:00
-- url     : https://prove2.me/theorems/0cf8e52d-3d52-4335-9342-9c224ae001c6
-- title:
--   Fixed Total: sum fixed Source Weight rpow central le
-- statement:
--   The fractional source weights on the central length window have the same
--   square-root bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralAggregate.lean#L89-L131
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralAggregate.lean#L89-L131

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

theorem CollatzEndpointTransport.FixedTotal.sum_fixedSourceWeight_rpow_central_le
    {N : ℕ} {theta eta : ℝ}
    (hN : 1 < N) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (∑ s ∈ centralLengthSet N eta,
        (fixedSourceWeight N s) ^ (1 - theta)) ≤
      fractionalBinomialMassConstant theta *
        (N : ℝ) ^ (theta / 2) := by sorry

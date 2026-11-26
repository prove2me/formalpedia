-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_central_fixed_total_aggregate_le_fixedSize
-- name    : CollatzEndpointTransport.FixedTotal.central_fixed_total_aggregate_le_fixedSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:51:25.334986+00:00
-- url     : https://prove2.me/theorems/4bb54615-2668-5b06-a794-abf2069116f6
-- title:
--   Fixed Total: central fixed total aggregate le fixed Size
-- statement:
--   Refined central aggregate with the manuscript's `N^(theta / 2)` scale.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralAggregate.lean#L134-L183
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralAggregate.lean#L134-L183

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

theorem CollatzEndpointTransport.FixedTotal.central_fixed_total_aggregate_le_fixedSize
    {N : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 2 < N)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N)
    (hinterior :
      ∀ s ∈ centralLengthSet N eta, 1 < s ∧ s < N) :
    (∑ s ∈ centralLengthSet N eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
      (fixedSizeCentralMomentConstant theta eta *
          fractionalBinomialMassConstant theta) *
        (N : ℝ) ^ (theta / 2) := by sorry

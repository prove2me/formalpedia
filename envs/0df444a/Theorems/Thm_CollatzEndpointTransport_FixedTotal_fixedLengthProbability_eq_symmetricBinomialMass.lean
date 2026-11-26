-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedLengthProbability_eq_symmetricBinomialMass
-- name    : CollatzEndpointTransport.FixedTotal.fixedLengthProbability_eq_symmetricBinomialMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:22:48.590543+00:00
-- url     : https://prove2.me/theorems/e4e62cd3-e758-5191-ab98-a348191e25a2
-- title:
--   Fixed Total: fixed Length Probability eq symmetric Binomial Mass
-- statement:
--   The composition-length law is exactly the symmetric binomial law on
--   `N - 1` separators.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralAggregate.lean#L30-L35
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralAggregate.lean#L30-L35

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

theorem CollatzEndpointTransport.FixedTotal.fixedLengthProbability_eq_symmetricBinomialMass
    {N s : ℕ} (hN : 0 < N) (hs : 0 < s) :
    fixedLengthProbability N s =
      symmetricBinomialMass (N - 1) (s - 1) := by sorry

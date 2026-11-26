-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_eq_half_fixedLengthProbability
-- name    : CollatzEndpointTransport.FixedTotal.fixedSourceWeight_eq_half_fixedLengthProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:23:26.799068+00:00
-- url     : https://prove2.me/theorems/93d29be5-0a72-4462-be98-28c83aaab815
-- title:
--   Fixed Total: fixed Source Weight eq half fixed Length Probability
-- statement:
--   The source weight used by the endpoint mixture is one half of the
--   composition-length probability.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralAggregate.lean#L39-L45
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralAggregate.lean#L39-L45

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

theorem CollatzEndpointTransport.FixedTotal.fixedSourceWeight_eq_half_fixedLengthProbability
    {N s : ℕ} (hN : 0 < N) :
    fixedSourceWeight N s = fixedLengthProbability N s / 2 := by sorry

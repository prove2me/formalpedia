-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_pow_le_succ_mul_scaledBinomialMass
-- name    : CollatzEndpointTransport.FixedTotal.pow_le_succ_mul_scaledBinomialMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:18.425457+00:00
-- url     : https://prove2.me/theorems/acbfae4c-0be7-4117-84bb-2eea4f9e6c48
-- title:
--   Fixed Total: pow le succ mul scaled Binomial Mass
-- statement:
--   Integer form of the binomial-mass-at-the-mean lower bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L799-L809
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L799-L809

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset

theorem CollatzEndpointTransport.FixedTotal.pow_le_succ_mul_scaledBinomialMass
    {n k : ℕ} (hk : k ≤ n) :
    n ^ n ≤ (n + 1) * scaledBinomialMass n k k := by sorry

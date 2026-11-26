-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_scaledBinomialMass_le_succ_of_lt_mean
-- name    : CollatzEndpointTransport.FixedTotal.scaledBinomialMass_le_succ_of_lt_mean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:22.611004+00:00
-- url     : https://prove2.me/theorems/efc467f4-27c9-4b8b-8fa3-b704fa86e40b
-- title:
--   Fixed Total: scaled Binomial Mass le succ of lt mean
-- statement:
--   The scaled masses increase strictly up to the mean index.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L698-L717
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L698-L717

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

theorem CollatzEndpointTransport.FixedTotal.scaledBinomialMass_le_succ_of_lt_mean
    {n k j : ℕ} (hk : k < n) (hj : j < k) :
    scaledBinomialMass n k j ≤ scaledBinomialMass n k (j + 1) := by sorry

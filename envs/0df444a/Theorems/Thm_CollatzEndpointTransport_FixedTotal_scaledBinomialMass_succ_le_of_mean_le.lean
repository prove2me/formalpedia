-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_scaledBinomialMass_succ_le_of_mean_le
-- name    : CollatzEndpointTransport.FixedTotal.scaledBinomialMass_succ_le_of_mean_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:14.373922+00:00
-- url     : https://prove2.me/theorems/4baf3a9c-0d46-498f-9fd4-2e7729508eb2
-- title:
--   Fixed Total: scaled Binomial Mass succ le of mean le
-- statement:
--   The scaled masses decrease after the mean index.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L720-L739
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L720-L739

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

theorem CollatzEndpointTransport.FixedTotal.scaledBinomialMass_succ_le_of_mean_le
    {n k j : ℕ} (hjn : j < n) (hkj : k ≤ j) :
    scaledBinomialMass n k (j + 1) ≤ scaledBinomialMass n k j := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_scaledBinomialMass_le_mode
-- name    : CollatzEndpointTransport.FixedTotal.scaledBinomialMass_le_mode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:11.35882+00:00
-- url     : https://prove2.me/theorems/e15c0830-1f92-4c80-a7b6-1a9308362239
-- title:
--   Fixed Total: scaled Binomial Mass le mode
-- statement:
--   Every scaled binomial mass is bounded by the mass at its mean index.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L742-L781
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L742-L781

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

theorem CollatzEndpointTransport.FixedTotal.scaledBinomialMass_le_mode
    {n k j : ℕ} (hk : k ≤ n) (hj : j ≤ n) :
    scaledBinomialMass n k j ≤ scaledBinomialMass n k k := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_natPow_rpow_eq_rpow_natPow
-- name    : CollatzEndpointTransport.FixedTotal.natPow_rpow_eq_rpow_natPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:34:35.034889+00:00
-- url     : https://prove2.me/theorems/1608c4ee-8f86-4e37-a79c-766d28c0635f
-- title:
--   Fixed Total: nat Pow rpow eq rpow nat Pow
-- statement:
--   Raising a natural power and then taking a real power commutes for a
--   nonnegative base.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L603-L607
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L603-L607

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.natPow_rpow_eq_rpow_natPow
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (theta : ℝ) :
    (x ^ n) ^ theta = (x ^ theta) ^ n := by sorry

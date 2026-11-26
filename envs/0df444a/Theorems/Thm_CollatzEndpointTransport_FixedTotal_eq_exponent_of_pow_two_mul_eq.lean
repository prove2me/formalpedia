-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_eq_exponent_of_pow_two_mul_eq
-- name    : CollatzEndpointTransport.FixedTotal.eq_exponent_of_pow_two_mul_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:49.281889+00:00
-- url     : https://prove2.me/theorems/78f73054-fb3e-5874-bd16-f1752ab5812b
-- title:
--   Fixed Total: eq exponent of pow two mul eq
-- statement:
--   Equality of `2^a` times odd numbers determines the exponent.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalComposition.lean#L70-L96
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalComposition.lean#L70-L96

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat

theorem CollatzEndpointTransport.FixedTotal.eq_exponent_of_pow_two_mul_eq
    {a b x y : ℕ}
    (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : 2 ^ a * x = 2 ^ b * y) :
    a = b := by sorry

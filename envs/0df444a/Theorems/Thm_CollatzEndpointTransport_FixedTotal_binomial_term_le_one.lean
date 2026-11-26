-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomial_term_le_one
-- name    : CollatzEndpointTransport.FixedTotal.binomial_term_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:16.924802+00:00
-- url     : https://prove2.me/theorems/1a08c04e-ebf5-5d79-974f-57af7c45f8a4
-- title:
--   Fixed Total: binomial term le one
-- statement:
--   One term of a binomial expansion with nonnegative parameters summing
--   to one is at most one.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L845-L865
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L845-L865

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

theorem CollatzEndpointTransport.FixedTotal.binomial_term_le_one
    {n k : ℕ} {p q : ℝ}
    (hk : k ≤ n) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    (n.choose k : ℝ) * p ^ k * q ^ (n - k) ≤ 1 := by sorry

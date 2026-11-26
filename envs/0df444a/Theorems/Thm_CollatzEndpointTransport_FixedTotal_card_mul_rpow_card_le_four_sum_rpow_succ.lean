-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_mul_rpow_card_le_four_sum_rpow_succ
-- name    : CollatzEndpointTransport.FixedTotal.card_mul_rpow_card_le_four_sum_rpow_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:44.329271+00:00
-- url     : https://prove2.me/theorems/b51897e9-e69f-5fd3-8a8d-e7e7a2656c1e
-- title:
--   Fixed Total: card mul rpow card le four sum rpow succ
-- statement:
--   Cardinality versus a positive real power of distinct nonnegative
--   integers.  The constant is uniform for `0 < theta <= 1`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L400-L472
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L400-L472

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
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.card_mul_rpow_card_le_four_sum_rpow_succ
    (S : Finset ℕ) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    (S.card : ℝ) * (S.card : ℝ) ^ theta ≤
      4 * ∑ q ∈ S, ((q + 1 : ℕ) : ℝ) ^ theta := by sorry

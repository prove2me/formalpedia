-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_mul_sqrt_card_le_four_sum_sqrt_succ
-- name    : CollatzEndpointTransport.FixedTotal.card_mul_sqrt_card_le_four_sum_sqrt_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:05.483881+00:00
-- url     : https://prove2.me/theorems/66f206eb-49bc-5088-922e-3fc80adbb593
-- title:
--   Fixed Total: card mul sqrt card le four sum sqrt succ
-- statement:
--   A cardinality-vs-square-root estimate for any finite set of distinct
--   nonnegative integers.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalQuotientOrder.lean#L73-L137
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalQuotientOrder.lean#L73-L137

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.card_mul_sqrt_card_le_four_sum_sqrt_succ
    (S : Finset ℕ) :
    (S.card : ℝ) * Real.sqrt S.card ≤
      4 * ∑ q ∈ S, Real.sqrt (q + 1) := by sorry

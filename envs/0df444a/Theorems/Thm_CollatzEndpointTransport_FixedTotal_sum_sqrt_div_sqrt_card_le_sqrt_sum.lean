-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_sqrt_div_sqrt_card_le_sqrt_sum
-- name    : CollatzEndpointTransport.FixedTotal.sum_sqrt_div_sqrt_card_le_sqrt_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:24:24.72629+00:00
-- url     : https://prove2.me/theorems/c4c1eea6-e8bb-4d46-937d-05bb5ca05926
-- title:
--   Fixed Total: sum sqrt div sqrt card le sqrt sum
-- statement:
--   Finite Cauchy--Schwarz in square-root form.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L80-L113
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L80-L113

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.compositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.sum_sqrt_div_sqrt_card_le_sqrt_sum
    {α : Type*} [DecidableEq α]
    (W : Finset α) (q : α → ℕ) :
    (∑ x ∈ W, Real.sqrt (q x)) / Real.sqrt W.card ≤
      Real.sqrt (∑ x ∈ W, q x) := by sorry

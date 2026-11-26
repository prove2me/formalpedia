-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_aggregateQ_le
-- name    : CollatzEndpointTransport.FixedTotal.aggregateQ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:24:24.00593+00:00
-- url     : https://prove2.me/theorems/88a29471-3f9d-4737-91df-0bafadb26695
-- title:
--   Fixed Total: aggregate Q le
-- statement:
--   The Fixed Total construction uses the aggregate Q le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L164-L209
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L164-L209

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

theorem CollatzEndpointTransport.FixedTotal.aggregateQ_le
    (N : ℕ) (hN : 0 < N) :
    (∑ s ∈ Finset.Icc 1 N,
        ∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)) ≤
      4 * N * 4 ^ (N - 1) := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fixedSet
-- name    : CollatzEndpointTransport.FixedTotal.sum_fixedSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:16.048055+00:00
-- url     : https://prove2.me/theorems/83e45a25-32fc-4acd-87da-e92cf3080851
-- title:
--   Fixed Total: sum fixed Set
-- statement:
--   The Fixed Total construction uses the sum fixed Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L147-L162
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L147-L162

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

theorem CollatzEndpointTransport.FixedTotal.sum_fixedSet
    (N : ℕ) (hN : 0 < N) (f : Composition N → ℕ) :
    (∑ s ∈ Finset.Icc 1 N, ∑ c ∈ fixedSet N s, f c) =
      ∑ c : Composition N, f c := by sorry

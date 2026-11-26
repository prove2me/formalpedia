-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedCriticalNumerator_le
-- name    : CollatzEndpointTransport.FixedTotal.fixedCriticalNumerator_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:24:10.401322+00:00
-- url     : https://prove2.me/theorems/a705183f-9c6f-4679-a089-f5f99c7aa63c
-- title:
--   Fixed Total: fixed Critical Numerator le
-- statement:
--   The Fixed Total construction uses the fixed Critical Numerator le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L68-L77
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L68-L77

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

theorem CollatzEndpointTransport.FixedTotal.fixedCriticalNumerator_le
    (N s : ℕ) :
    fixedCriticalNumerator N s ≤
      4 * ∑ c ∈ fixedSet N s,
        Real.sqrt (3 ^ s + syracuseNumerator c) := by sorry

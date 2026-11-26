-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_injOn_fixedSet
-- name    : CollatzEndpointTransport.FixedTotal.syracuseNumerator_injOn_fixedSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:24:01.515502+00:00
-- url     : https://prove2.me/theorems/5fb4f78d-a893-5b7a-9c92-70b0dfc9aab9
-- title:
--   Fixed Total: syracuse Numerator inj On fixed Set
-- statement:
--   The Fixed Total construction uses the syracuse Numerator inj On fixed Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L39-L46
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L39-L46

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

theorem CollatzEndpointTransport.FixedTotal.syracuseNumerator_injOn_fixedSet
    (N s : ℕ) :
    Set.InjOn syracuseNumerator (↑(fixedSet N s) : Set (Composition N)) := by sorry

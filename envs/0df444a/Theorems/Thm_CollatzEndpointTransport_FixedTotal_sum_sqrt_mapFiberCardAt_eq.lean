-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_sqrt_mapFiberCardAt_eq
-- name    : CollatzEndpointTransport.FixedTotal.sum_sqrt_mapFiberCardAt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:54:46.750959+00:00
-- url     : https://prove2.me/theorems/17489e21-1845-5a08-98ad-d67047015128
-- title:
--   Fixed Total: sum sqrt map Fiber Card At eq
-- statement:
--   The Fixed Total construction uses the sum sqrt map Fiber Card At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L49-L77
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L49-L77

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.endpointCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.sum_sqrt_mapFiberCardAt_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (W : Finset α) (f : α → β) :
    (∑ x ∈ W, Real.sqrt (mapFiberCardAt W f x)) =
      ∑ b : β,
        (mapFiber W f b).card * Real.sqrt (mapFiber W f b).card := by sorry

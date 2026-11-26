-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_mapFiberCardAt_rpow_eq
-- name    : CollatzEndpointTransport.FixedTotal.sum_mapFiberCardAt_rpow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:01:25.215795+00:00
-- url     : https://prove2.me/theorems/8a8ba42e-1e53-4079-80bf-45658f59d3c3
-- title:
--   Fixed Total: sum map Fiber Card At rpow eq
-- statement:
--   The Fixed Total construction uses the sum map Fiber Card At rpow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L152-L179
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L152-L179

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralEndpointCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.sum_mapFiberCardAt_rpow_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (W : Finset α) (f : α → β) (theta : ℝ) :
    (∑ x ∈ W, ((mapFiberCardAt W f x : ℕ) : ℝ) ^ theta) =
      ∑ b : β, ((mapFiber W f b).card : ℝ) *
        ((mapFiber W f b).card : ℝ) ^ theta := by sorry

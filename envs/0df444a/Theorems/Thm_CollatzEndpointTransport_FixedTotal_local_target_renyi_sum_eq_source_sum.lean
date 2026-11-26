-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_local_target_renyi_sum_eq_source_sum
-- name    : CollatzEndpointTransport.FixedTotal.local_target_renyi_sum_eq_source_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:02:35.337962+00:00
-- url     : https://prove2.me/theorems/084a1450-589d-43e5-88d9-2ced533c4d26
-- title:
--   Fixed Total: local target renyi sum eq source sum
-- statement:
--   The Fixed Total construction uses the local target renyi sum eq source sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L47-L95
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L47-L95

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

theorem CollatzEndpointTransport.FixedTotal.local_target_renyi_sum_eq_source_sum
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β)
    {i : ι} (hi : i ∈ U) {theta : ℝ} (htheta : 0 < theta) :
    (∑ b ∈ mixedTargetSet U W f,
        ((mapFiber (W i) (f i) b).card : ℝ) ^ (1 + theta)) =
      ∑ x ∈ W i,
        ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by sorry

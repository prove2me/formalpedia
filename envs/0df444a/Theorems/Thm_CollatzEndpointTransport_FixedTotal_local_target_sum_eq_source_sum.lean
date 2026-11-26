-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_local_target_sum_eq_source_sum
-- name    : CollatzEndpointTransport.FixedTotal.local_target_sum_eq_source_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:55:32.061901+00:00
-- url     : https://prove2.me/theorems/2efd1f49-1636-4dd9-a0a8-6b03a104edc7
-- title:
--   Fixed Total: local target sum eq source sum
-- statement:
--   The Fixed Total construction uses the local target sum eq source sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FiniteFiberMixture.lean#L108-L146
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FiniteFiberMixture.lean#L108-L146

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.local_target_sum_eq_source_sum
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β)
    {i : ι} (hi : i ∈ U) :
    (∑ b ∈ mixedTargetSet U W f,
        (mapFiber (W i) (f i) b).card *
          Real.sqrt (mapFiber (W i) (f i) b).card) =
      ∑ x ∈ W i, Real.sqrt (mapFiberCardAt (W i) (f i) x) := by sorry

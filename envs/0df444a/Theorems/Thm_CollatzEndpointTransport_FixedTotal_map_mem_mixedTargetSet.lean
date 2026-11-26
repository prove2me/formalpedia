-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_map_mem_mixedTargetSet
-- name    : CollatzEndpointTransport.FixedTotal.map_mem_mixedTargetSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:54:19.622636+00:00
-- url     : https://prove2.me/theorems/5cf9b781-34f8-5ac3-994e-1992e8550d3a
-- title:
--   Fixed Total: map mem mixed Target Set
-- statement:
--   The Fixed Total construction uses the map mem mixed Target Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FiniteFiberMixture.lean#L98-L106
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FiniteFiberMixture.lean#L98-L106

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.map_mem_mixedTargetSet
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β)
    {i : ι} (hi : i ∈ U) {x : α i} (hx : x ∈ W i) :
    f i x ∈ mixedTargetSet U W f := by sorry

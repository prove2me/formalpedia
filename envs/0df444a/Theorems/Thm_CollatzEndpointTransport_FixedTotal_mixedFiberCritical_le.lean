-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_mixedFiberCritical_le
-- name    : CollatzEndpointTransport.FixedTotal.mixedFiberCritical_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:56:35.212723+00:00
-- url     : https://prove2.me/theorems/ab9b6de7-d558-49cb-8afc-fc0e873763ca
-- title:
--   Fixed Total: mixed Fiber Critical le
-- statement:
--   Critical `3/2` mixture bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FiniteFiberMixture.lean#L149-L181
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FiniteFiberMixture.lean#L149-L181

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.mixedFiberCritical_le
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β) :
    (∑ b ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f b : ℝ) *
          Real.sqrt (mixedFiberCard U W f b)) ≤
      Real.sqrt U.card *
        ∑ i ∈ U, ∑ x ∈ W i,
          Real.sqrt (mapFiberCardAt (W i) (f i) x) := by sorry

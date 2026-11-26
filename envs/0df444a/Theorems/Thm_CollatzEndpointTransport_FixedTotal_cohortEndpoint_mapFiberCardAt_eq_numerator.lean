-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortEndpoint_mapFiberCardAt_eq_numerator
-- name    : CollatzEndpointTransport.FixedTotal.cohortEndpoint_mapFiberCardAt_eq_numerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:54:10.429809+00:00
-- url     : https://prove2.me/theorems/58ddc5df-f825-420c-9c32-5f07c5861c31
-- title:
--   Fixed Total: cohort Endpoint map Fiber Card At eq numerator
-- statement:
--   The Fixed Total construction uses the cohort Endpoint map Fiber Card At eq numerator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L146-L154
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L146-L154

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.endpointCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.cohortEndpoint_mapFiberCardAt_eq_numerator
    {M s : ℕ} (u : Fin M)
    {c : Composition (M - (u : ℕ))}
    (hc : c ∈ fixedSet (M - (u : ℕ)) s) :
    mapFiberCardAt (fixedSet (M - (u : ℕ)) s)
        (cohortEndpoint u) c =
      mapFiberCardAt (fixedSet (M - (u : ℕ)) s)
        (cohortNumeratorResidue (s := s)) c := by sorry

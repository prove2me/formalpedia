-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortEndpoint_mapFiber_eq_numerator
-- name    : CollatzEndpointTransport.FixedTotal.cohortEndpoint_mapFiber_eq_numerator
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:54:52.223927+00:00
-- url     : https://prove2.me/theorems/9c7aaffc-e4b0-53f1-a502-61f79dfd0e3e
-- title:
--   Fixed Total: cohort Endpoint map Fiber eq numerator
-- statement:
--   Exact equality of the endpoint fiber and normalized-correction fiber
--   through a source in one fixed cohort.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L129-L144
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L129-L144

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.endpointCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.cohortEndpoint_mapFiber_eq_numerator
    {M s : ℕ} (u : Fin M)
    {c : Composition (M - (u : ℕ))}
    (hc : c ∈ fixedSet (M - (u : ℕ)) s) :
    mapFiber (fixedSet (M - (u : ℕ)) s)
        (cohortEndpoint u) (cohortEndpoint u c) =
      mapFiber (fixedSet (M - (u : ℕ)) s)
        (cohortNumeratorResidue (s := s))
        (cohortNumeratorResidue (s := s) c) := by sorry

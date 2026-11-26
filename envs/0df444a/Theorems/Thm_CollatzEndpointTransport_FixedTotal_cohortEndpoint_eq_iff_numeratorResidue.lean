-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortEndpoint_eq_iff_numeratorResidue
-- name    : CollatzEndpointTransport.FixedTotal.cohortEndpoint_eq_iff_numeratorResidue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:55:54.47712+00:00
-- url     : https://prove2.me/theorems/6a44d0c8-52ce-4bf5-8540-09ad17ac891f
-- title:
--   Fixed Total: cohort Endpoint eq iff numerator Residue
-- statement:
--   Within one first-odd and odd-count cohort, the endpoint fibers and the
--   normalized-correction residue fibers are exactly the same.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L92-L125
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L92-L125

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.endpointCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.cohortEndpoint_eq_iff_numeratorResidue
    {M s : ℕ} (u : Fin M)
    {c d : Composition (M - (u : ℕ))}
    (hc : c ∈ fixedSet (M - (u : ℕ)) s)
    (hd : d ∈ fixedSet (M - (u : ℕ)) s) :
    cohortEndpoint u c = cohortEndpoint u d ↔
      cohortNumeratorResidue (s := s) c =
        cohortNumeratorResidue (s := s) d := by sorry

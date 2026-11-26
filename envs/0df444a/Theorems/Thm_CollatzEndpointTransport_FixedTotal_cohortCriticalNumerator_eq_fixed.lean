-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortCriticalNumerator_eq_fixed
-- name    : CollatzEndpointTransport.FixedTotal.cohortCriticalNumerator_eq_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:55:56.244056+00:00
-- url     : https://prove2.me/theorems/cbacbaa7-f0c9-4fd1-be0b-d520b7871cb7
-- title:
--   Fixed Total: cohort Critical Numerator eq fixed
-- statement:
--   **Exact fixed-cohort endpoint-to-correction bridge.**
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L175-L208
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L175-L208

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.endpointCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.cohortCriticalNumerator_eq_fixed
    (M : ℕ) (u : Fin M) (s : ℕ) :
    cohortCriticalNumerator M u s =
      fixedCriticalNumerator (M - (u : ℕ)) s := by sorry

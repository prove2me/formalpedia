-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortCriticalNumerator_le
-- name    : CollatzEndpointTransport.FixedTotal.cohortCriticalNumerator_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:54:58.732386+00:00
-- url     : https://prove2.me/theorems/43ff4ad6-ed83-54ea-935c-9d2341e5e46b
-- title:
--   Fixed Total: cohort Critical Numerator le
-- statement:
--   Backward-compatible inequality form of the exact bridge.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L211-L215
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L211-L215

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.endpointCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.cohortCriticalNumerator_le
    (M : ℕ) (u : Fin M) (s : ℕ) :
    cohortCriticalNumerator M u s ≤
      fixedCriticalNumerator (M - (u : ℕ)) s := by sorry

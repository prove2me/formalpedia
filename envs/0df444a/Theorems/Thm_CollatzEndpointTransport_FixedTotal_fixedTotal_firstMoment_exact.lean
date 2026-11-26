-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedTotal_firstMoment_exact
-- name    : CollatzEndpointTransport.FixedTotal.fixedTotal_firstMoment_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:58.891877+00:00
-- url     : https://prove2.me/theorems/c4aac879-7715-5af4-92b1-ef4d422baa73
-- title:
--   Fixed Total: fixed Total first Moment exact
-- statement:
--   Exact aggregate first-moment identity.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalFirstMoment.lean#L197-L209
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalFirstMoment.lean#L197-L209

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedTotal_firstMoment_exact
    (N : ℕ) (hN : 0 < N) :
    2 * (∑ c : Composition N,
        (3 ^ c.length + syracuseNumerator c)) =
      (N + 7) * 4 ^ (N - 1) := by sorry

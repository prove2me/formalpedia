-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedCriticalAverage_le
-- name    : CollatzEndpointTransport.FixedTotal.fixedCriticalAverage_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:07.759926+00:00
-- url     : https://prove2.me/theorems/da7e8c57-36df-57f1-824f-e4d7c2ba4715
-- title:
--   Fixed Total: fixed Critical Average le
-- statement:
--   **Critical fixed-total theorem.**
--
--   The averaged normalized residue moment grows at most linearly.  The constant
--   `8` reflects the deliberately robust quotient-order factor `4`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L215-L295
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L215-L295

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.compositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.fixedCriticalAverage_le
    (N : ℕ) (hN : 0 < N) :
    fixedCriticalAverage N ≤ 8 * N := by sorry

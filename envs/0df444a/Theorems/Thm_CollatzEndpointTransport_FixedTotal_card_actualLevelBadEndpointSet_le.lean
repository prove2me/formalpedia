-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_actualLevelBadEndpointSet_le
-- name    : CollatzEndpointTransport.FixedTotal.card_actualLevelBadEndpointSet_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:59:31.751468+00:00
-- url     : https://prove2.me/theorems/bba1a65c-6410-50aa-adab-c1e6a2d9a69b
-- title:
--   Fixed Total: card actual Level Bad Endpoint Set le
-- statement:
--   A `(C,D)`-dense target has at most `C R^(1-D)` bad possible endpoints
--   at level `s`, where `R=3^(s+1)`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointTarget.lean#L149-L167
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointTarget.lean#L149-L167

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointTarget
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.card_actualLevelBadEndpointSet_le
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M s : ℕ) :
    ((actualLevelBadEndpointSet S M s).card : ℝ) ≤
      C * (3 ^ (s + 1) : ℝ) ^ (1 - D) := by sorry

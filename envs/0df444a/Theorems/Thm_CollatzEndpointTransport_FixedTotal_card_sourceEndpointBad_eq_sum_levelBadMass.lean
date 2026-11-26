-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceEndpointBad_eq_sum_levelBadMass
-- name    : CollatzEndpointTransport.FixedTotal.card_sourceEndpointBad_eq_sum_levelBadMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:24.531883+00:00
-- url     : https://prove2.me/theorems/0d0cfa2f-17f0-4a00-94d6-215a2d7c95e2
-- title:
--   Fixed Total: card source Endpoint Bad eq sum level Bad Mass
-- statement:
--   Exact decomposition of the full source-code failure count.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointTarget.lean#L91-L125
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointTarget.lean#L91-L125

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointTarget
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.card_sourceEndpointBad_eq_sum_levelBadMass
    (S : Set ℕ) (M : ℕ) :
    (sourceEndpointBad S M).card =
      ∑ s ∈ Finset.range (M + 1),
        actualLevelBadMass S M s := by sorry

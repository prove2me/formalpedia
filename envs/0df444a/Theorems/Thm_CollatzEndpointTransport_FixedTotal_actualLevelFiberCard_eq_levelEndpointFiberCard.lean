-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualLevelFiberCard_eq_levelEndpointFiberCard
-- name    : CollatzEndpointTransport.FixedTotal.actualLevelFiberCard_eq_levelEndpointFiberCard
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:58:29.90973+00:00
-- url     : https://prove2.me/theorems/d6788294-969b-4928-88e4-8872fe52dd74
-- title:
--   Fixed Total: actual Level Fiber Card eq level Endpoint Fiber Card
-- statement:
--   The Fixed Total construction uses the actual Level Fiber Card eq level Endpoint Fiber Card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalActualEndpointMoment.lean#L49-L68
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalActualEndpointMoment.lean#L49-L68

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.actualLevelFiberCard_eq_levelEndpointFiberCard
    {M s y : ℕ} (hs : 0 < s) :
    actualLevelFiberCard M s y =
      levelEndpointFiberCard M s y := by sorry

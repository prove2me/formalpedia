-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_levelSourceCard_eq_card_sourceOddLevel
-- name    : CollatzEndpointTransport.FixedTotal.levelSourceCard_eq_card_sourceOddLevel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:58:39.206152+00:00
-- url     : https://prove2.me/theorems/56b8e89f-f753-4af1-85de-5ebf2bae4cea
-- title:
--   Fixed Total: level Source Card eq card source Odd Level
-- statement:
--   The Fixed Total construction uses the level Source Card eq card source Odd Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalActualEndpointMoment.lean#L70-L87
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalActualEndpointMoment.lean#L70-L87

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.levelSourceCard_eq_card_sourceOddLevel
    {M s : ℕ} (hs : 0 < s) :
    levelSourceCard M s = (sourceOddLevel M s).card := by sorry

-- Prove2me | Theorems.Thm_Csg_skirmish_wet_not_mem_Pre1
-- name    : Csg.skirmish_wet_not_mem_Pre1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:24:21.154134+00:00
-- url     : https://prove2.me/theorems/f7d2bfc0-500d-459b-bbe1-258cdd95da23
-- title:
--   Csg: skirmish wet not mem Pre1
-- statement:
--   **The payoff, the `Pre1` sibling of `skirmish_wet_not_mem_Apre1`.** `wet`'s transition is
--       constant (`skirmishK_wet`), so its support can only ever meet a target `x` that already
--       contains `wet` -- if it doesn't, `wet` fails `Pre1`'s existential outright, using the concrete
--       witness `SniperMove.wait` rather than needing to range over every column action.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1199-L1205
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1199-L1205

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_wet_not_mem_Pre1 (x : Set SkirmishPos) (hx : SkirmishPos.wet ∉ x) :
    SkirmishPos.wet ∉ skirmishCSG.Pre1 x := by sorry

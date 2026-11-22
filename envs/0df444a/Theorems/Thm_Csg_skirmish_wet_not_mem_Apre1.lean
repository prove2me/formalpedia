-- Prove2me | Theorems.Thm_Csg_skirmish_wet_not_mem_Apre1
-- name    : Csg.skirmish_wet_not_mem_Apre1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:00:01.359304+00:00
-- url     : https://prove2.me/theorems/bff66f4d-a8ed-4a6d-819f-3b6477ed25c0
-- title:
--   Csg: skirmish wet not mem Apre1
-- statement:
--   **The payoff, general beyond this section.** `wet`'s transition is constant (`skirmishK_wet`):
--       whatever the joint move, the outcome is `wet` again, so its support can only ever meet a
--       target `x` that already contains `wet`. If `x` doesn't, `B _ x wet` is `∅` for *any* row-action
--       pool -- not just the specific one `A ∅ y wet` computes -- so `wet` fails `Apre1 x y`'s
--       `B (...) = univ` test outright, regardless of `y`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L352-L364
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L352-L364

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_wet_not_mem_Apre1 (x y : Set SkirmishPos) (hx : SkirmishPos.wet ∉ x) :
    SkirmishPos.wet ∉ skirmishCSG.Apre1 x y := by sorry

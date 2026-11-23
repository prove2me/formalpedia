-- Prove2me | Theorems.Thm_Csg_skirmish_safe_le_LFOuter_safe
-- name    : Csg.skirmish_safe_le_LFOuter_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:18:19.921652+00:00
-- url     : https://prove2.me/theorems/f4870544-4d05-4b40-959f-03b5168c6b49
-- title:
--   Csg: skirmish safe le LFOuter safe
-- statement:
--   **The payoff.** `skirmishSafe` is a post-fixed point of `LFOuter {home}`, in exactly two steps
--       up from `⊥`: `∅ ↦ {home} ↦ skirmishSafe` (`home` trivially, via the union with `b`; `hide` via
--       `skirmish_hide_mem_Lpre1_home_safe`). `OrderHom.map_map_bot_le_lfp` turns this into a genuine
--       lower bound on the inner `lfp`, handing `OrderHom.le_gfp` exactly the post-fixed-point
--       hypothesis it needs.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L592-L612
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L592-L612

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_safe_le_LFOuter_safe :
    skirmishSafe ≤ skirmishCSG.LFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe := by sorry

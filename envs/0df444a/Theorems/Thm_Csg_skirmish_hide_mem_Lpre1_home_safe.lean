-- Prove2me | Theorems.Thm_Csg_skirmish_hide_mem_Lpre1_home_safe
-- name    : Csg.skirmish_hide_mem_Lpre1_home_safe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:05:56.652059+00:00
-- url     : https://prove2.me/theorems/61f749d8-88ec-48f7-a4b3-50d91bc273d9
-- title:
--   Csg: skirmish hide mem Lpre1 home safe
-- statement:
--   **The payoff.** `hide` qualifies for `Lpre1 {home} skirmishSafe` outright: its `LW` witness set
--       reaches `Set.univ` (`skirmish_LW_home_safe_hide_eq_univ`), and `Set.univ` escapes into `{home}`
--       against every sniper response (`skirmish_B_univ_home_hide_eq_univ`) -- exactly `Lpre1`'s own
--       `B (...) = univ` test.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L577-L583
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L577-L583

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_mem_Lpre1_home_safe :
    SkirmishPos.hide ∈ skirmishCSG.Lpre1 ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe := by sorry

-- Prove2me | Theorems.Thm_Csg_skirmishReachGoal_pre1_empty
-- name    : Csg.skirmishReachGoal_pre1_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:04:57.003136+00:00
-- url     : https://prove2.me/theorems/9ce39a1a-413e-43a9-9fde-ed493167d507
-- title:
--   Csg: skirmish Reach Goal pre1 empty
-- statement:
--   **The payoff.** No state -- not even `home` itself -- has a row action that forces landing
--       back in `{home}` in one more step against *every* sniper response: `wet` and `home` both
--       ignore the joint move entirely and land somewhere else (`wet`/`hide` respectively, checked
--       against any witness sniper move); `hide` fails for both its own row actions (`hide` loses to
--       `(hide,wait)→hide`, `run` loses to `(run,throw)→wet`). The dual of `skirmishSafe_pre1`, which
--       showed `safe` *does* sustain itself; here `{home}` provably does not.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L292-L316
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L292-L316

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmishReachGoal_pre1_empty :
    skirmishCSG.Pre1 ({SkirmishPos.home} : Set SkirmishPos) = ∅ := by sorry

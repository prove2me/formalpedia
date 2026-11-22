-- Prove2me | Theorems.Thm_Csg_combine_hiderC_thrower
-- name    : Csg.combine_hiderC_thrower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:02:38.918781+00:00
-- url     : https://prove2.me/theorems/b116e7e8-9b93-4f8a-8b34-801fa20a105a
-- title:
--   Csg: combine hider C thrower
-- statement:
--   `NCSG.combine hiderC`, evaluated at `thrower`, is exactly `throwerComplementEquiv`'s own
--       reading of the complement's action.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L155-L157
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L155-L157

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition
set_option autoImplicit true
open Csg

theorem Csg.combine_hiderC_thrower (aC : NCSG.CoalitionAction SkirmishAction hiderC)
    (aC' : NCSG.ComplementAction SkirmishAction hiderC) :
    NCSG.combine hiderC aC aC' SkirmishPlayer.thrower = throwerComplementEquiv aC' := by sorry

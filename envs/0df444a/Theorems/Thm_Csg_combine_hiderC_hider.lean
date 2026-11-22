-- Prove2me | Theorems.Thm_Csg_combine_hiderC_hider
-- name    : Csg.combine_hiderC_hider
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:01:43.709817+00:00
-- url     : https://prove2.me/theorems/99915043-0475-45c3-9341-b3f98f4f7e63
-- title:
--   Csg: combine hider C hider
-- statement:
--   `NCSG.combine hiderC`, evaluated at `hider`, is exactly `hiderSingletonEquiv`'s own reading of
--       the coalition's action -- the singleton-coalition analogue of
--       `Csg.CoalitionComplement.combine_compl`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L149-L151
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L149-L151

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition
set_option autoImplicit true
open Csg

theorem Csg.combine_hiderC_hider (aC : NCSG.CoalitionAction SkirmishAction hiderC)
    (aC' : NCSG.ComplementAction SkirmishAction hiderC) :
    NCSG.combine hiderC aC aC' SkirmishPlayer.hider = hiderSingletonEquiv aC := by sorry

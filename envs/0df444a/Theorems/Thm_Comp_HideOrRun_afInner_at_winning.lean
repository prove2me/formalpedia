-- Prove2me | Theorems.Thm_Comp_HideOrRun_afInner_at_winning
-- name    : Comp.HideOrRun.afInner_at_winning
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:02:22.416704+00:00
-- url     : https://prove2.me/theorems/9054425b-6520-4ad2-9f86-aee483668e2b
-- title:
--   Hide Or Run: af Inner at winning
-- statement:
--   The second outer step, where almost-sure mode loses `live`. Restricted to the row actions that
--       are safe for `winning`, the runner can only *wait* -- running risks `dead`, which lies outside
--       `winning` -- and waiting against a wait returns to `live`. So the middle chain never grows past
--       the goal itself.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L331-L334
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L331-L334

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun

theorem Comp.HideOrRun.afInner_at_winning :
    ((game.toCSG game_wf).AFInner ↑target ↑winning).lfp = (↑target : Set HR) := by sorry

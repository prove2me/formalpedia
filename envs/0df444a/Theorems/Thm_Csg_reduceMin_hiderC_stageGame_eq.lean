-- Prove2me | Theorems.Thm_Csg_reduceMin_hiderC_stageGame_eq
-- name    : Csg.reduceMin_hiderC_stageGame_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:27:39.314183+00:00
-- url     : https://prove2.me/theorems/8455616a-0a22-4e36-a6eb-0a86c8d2f93c
-- title:
--   Csg: reduce Min hider C stage Game eq
-- statement:
--   `⟨⟨hider⟩⟩ P_min`'s stage game at `s_hide` is literally `skirmishMinCSG`'s own stage game, both
--       its row and column index types relabelled along `hiderSingletonEquiv`/`throwerComplementEquiv`
--       -- `Csg.CoalitionComplement.reduceMin_stageValue_eq`'s own `funext`/`congrArg MatrixGame.mk`
--       technique, reused verbatim.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L165-L179
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L165-L179

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition
set_option autoImplicit true
open Csg

theorem Csg.reduceMin_hiderC_stageGame_eq (v : SkirmishState → ℝ) :
    (skirmishNCSG.reduceMin hiderC).stageGame .hide v =
      ((skirmishMinCSG.stageGame .hide v).relabelRow hiderSingletonEquiv).relabelCol
        throwerComplementEquiv := by sorry

-- Prove2me | Theorems.Thm_Csg_reduceMax_hiderC_stageGame_eq
-- name    : Csg.reduceMax_hiderC_stageGame_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:29:18.75297+00:00
-- url     : https://prove2.me/theorems/3d5aab21-ab23-4202-a6de-44a3bc1f98b8
-- title:
--   Csg: reduce Max hider C stage Game eq
-- statement:
--   `⟨⟨hider⟩⟩ P_max`'s stage game at `s_hide` is literally `skirmishMaxCSG`'s own stage game,
--       row and column relabelled the other way round -- `throwerComplementEquiv` on the row side
--       (`reduceMax`'s row slot is the complement), `hiderSingletonEquiv` on the column side.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L195-L209
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L195-L209

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition
set_option autoImplicit true
open Csg

theorem Csg.reduceMax_hiderC_stageGame_eq (v : SkirmishState → ℝ) :
    (skirmishNCSG.reduceMax hiderC).stageGame .hide v =
      ((skirmishMaxCSG.stageGame .hide v).relabelRow throwerComplementEquiv).relabelCol
        hiderSingletonEquiv := by sorry

-- Prove2me | Theorems.Thm_Csg_reduceMin_hiderC_stageValue_eq
-- name    : Csg.reduceMin_hiderC_stageValue_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:27:47.529309+00:00
-- url     : https://prove2.me/theorems/39e6dba7-9c90-4a5c-b488-2e8e84229345
-- title:
--   Csg: reduce Min hider C stage Value eq
-- statement:
--   **`⟨⟨hider⟩⟩ P_min`.** With `hider` reduced to the row/minimising side (`Csg.Coalition`'s own
--       reading of `⟨⟨hider⟩⟩ P_min`), the stage value at `s_hide` is exactly `4/5` -- the same number
--       `Csg.SkirmishFeint.stageValue_min_eq` already established for the hand-built two-player game,
--       now transported through the genuine `NCSG`/`Coalition` reduction.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L185-L190
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L185-L190

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition
set_option autoImplicit true
open Csg

theorem Csg.reduceMin_hiderC_stageValue_eq (v : SkirmishState → ℝ) (vhide : v .hide = 4 / 5)
    (vhome : v .home = 1) (vwet : v .wet = 0) :
    (skirmishNCSG.reduceMin hiderC).stageValue .hide v = 4 / 5 := by sorry

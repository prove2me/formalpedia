-- Prove2me | Theorems.Thm_Csg_reduceMax_hiderC_stageValue_eq
-- name    : Csg.reduceMax_hiderC_stageValue_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:29:20.998869+00:00
-- url     : https://prove2.me/theorems/c4b978cd-f702-4fb7-a6ee-98d3e95b9efc
-- title:
--   Csg: reduce Max hider C stage Value eq
-- statement:
--   **`⟨⟨hider⟩⟩ P_max`.** With `hider` reduced to the column/maximising side, the stage value at
--       `s_hide` is exactly `1/2` -- transporting `Csg.SkirmishFeint.stageValue_max_eq` through the
--       genuine reduction, mirror of `reduceMin_hiderC_stageValue_eq`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L214-L219
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L214-L219

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition
set_option autoImplicit true
open Csg

theorem Csg.reduceMax_hiderC_stageValue_eq (v : SkirmishState → ℝ) (vhide : v .hide = 1 / 2)
    (vhome : v .home = 1) (vwet : v .wet = 0) :
    (skirmishNCSG.reduceMax hiderC).stageValue .hide v = 1 / 2 := by sorry

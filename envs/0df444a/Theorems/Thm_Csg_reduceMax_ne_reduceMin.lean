-- Prove2me | Theorems.Thm_Csg_reduceMax_ne_reduceMin
-- name    : Csg.reduceMax_ne_reduceMin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:04:55.189104+00:00
-- url     : https://prove2.me/theorems/4b2534d9-f2f1-44a4-a86e-c9e54d79e1ff
-- title:
--   Csg: reduce Max ne reduce Min
-- statement:
--   **The point of this file.** `⟨⟨hider⟩⟩ P_max ≠ ⟨⟨hider⟩⟩ P_min` at `s_hide`, in
--       `Csg.Coalition`'s own `reduceMin`/`reduceMax` terms -- the FMSD-shaped statement
--       `Csg.SkirmishFeint.value_ne` anticipated, now stated over the genuine coalition reduction
--       rather than the two hand-built `CSG`s.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L225-L232
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean#L225-L232

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_SkirmishFeintCoalition
set_option autoImplicit true
open Csg

theorem Csg.reduceMax_ne_reduceMin (vMin vMax : SkirmishState → ℝ)
    (vMinHide : vMin .hide = 4 / 5) (vMinHome : vMin .home = 1) (vMinWet : vMin .wet = 0)
    (vMaxHide : vMax .hide = 1 / 2) (vMaxHome : vMax .home = 1) (vMaxWet : vMax .wet = 0) :
    (skirmishNCSG.reduceMax hiderC).stageValue .hide vMax ≠
      (skirmishNCSG.reduceMin hiderC).stageValue .hide vMin := by sorry

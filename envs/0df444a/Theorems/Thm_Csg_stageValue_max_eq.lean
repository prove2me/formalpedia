-- Prove2me | Theorems.Thm_Csg_stageValue_max_eq
-- name    : Csg.stageValue_max_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:01:14.222673+00:00
-- url     : https://prove2.me/theorems/9fab3c78-b851-4c6d-a913-5d0addfcd9eb
-- title:
--   Csg: stage Value max eq
-- statement:
--   **The `⟨⟨hider⟩⟩ P_max`-shaped value.** With the thrower row/minimising and the hider
--       column/maximising, the stage game at `s_hide` -- once the continuation already carries `s_hide`
--       itself at the self-consistent value `1/2` -- has value exactly `1/2`. Witnessed on the row side
--       by `throwerMaxMix` (`wait`/`feint`, `2/7`-`5/7`, `throw` unused) and on the column side by
--       `hiderPureHideCol` (always hide).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L356-L385
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L356-L385

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.stageValue_max_eq (v : SkirmishState → ℝ) (vhide : v .hide = 1 / 2) (vhome : v .home = 1)
    (vwet : v .wet = 0) :
    (skirmishMaxCSG.stageGame .hide v).value = 1 / 2 := by sorry

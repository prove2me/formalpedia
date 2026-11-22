-- Prove2me | Theorems.Thm_Csg_stageValue_min_eq
-- name    : Csg.stageValue_min_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:00:33.642794+00:00
-- url     : https://prove2.me/theorems/c4b77a4a-8313-4567-9240-8777eebd6719
-- title:
--   Csg: stage Value min eq
-- statement:
--   **The `⟨⟨hider⟩⟩ P_min`-shaped value.** With the hider row/minimising and the thrower
--       column/maximising, the stage game at `s_hide` -- once the continuation already carries `s_hide`
--       itself at the self-consistent value `4/5` -- has value exactly `4/5`. Witnessed on the row side
--       by `hiderPureHide` (always hide) and on the column side by `throwerMinMix`
--       (`wait`/`throw`, `4/5`-`1/5`) via `le_antisymm` between `MatrixGameLP.lean`'s two LP
--       characterizations, exactly the reuse that file's own docstring anticipated.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L308-L337
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L308-L337

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.stageValue_min_eq (v : SkirmishState → ℝ) (vhide : v .hide = 4 / 5) (vhome : v .home = 1)
    (vwet : v .wet = 0) :
    (skirmishMinCSG.stageGame .hide v).value = 4 / 5 := by sorry

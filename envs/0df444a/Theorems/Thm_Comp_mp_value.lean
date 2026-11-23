-- Prove2me | Theorems.Thm_Comp_mp_value
-- name    : Comp.mp_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:37:28.971806+00:00
-- url     : https://prove2.me/theorems/4b27ef33-9e39-4c50-82bc-c54781e03ab1
-- title:
--   Comp: mp value
-- statement:
--   **The value of matching pennies is zero.**
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/RockPaperScissorsQ.lean#L148-L149
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/RockPaperScissorsQ.lean#L148-L149

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Comp_RockPaperScissorsQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.mp_value : mpMatrixQ.toMatrixGame.value = 0 := by sorry

-- Prove2me | Theorems.Thm_Comp_twoGame_step
-- name    : Comp.twoGame_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:56:11.140318+00:00
-- url     : https://prove2.me/theorems/c4d2049a-e2d1-4086-a201-7d8b1bb472b5
-- title:
--   Comp: two Game step
-- statement:
--   `v2` is the Shapley image of `v1`, state by state.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L227-L232
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L227-L232

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.twoGame_step : ∀ s, (twoGame.toDiscountedCSG twoGame_wf).shapley
    (fun s' => ((v1 s' : ℚ) : ℝ)) s = ((v2 s : ℚ) : ℝ) := by sorry

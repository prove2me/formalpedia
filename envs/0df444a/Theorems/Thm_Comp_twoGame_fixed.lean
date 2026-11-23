-- Prove2me | Theorems.Thm_Comp_twoGame_fixed
-- name    : Comp.twoGame_fixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:54:52.148189+00:00
-- url     : https://prove2.me/theorems/874bc590-c110-409a-9e86-7b257fba072d
-- title:
--   Comp: two Game fixed
-- statement:
--   `vStar` is a fixed point of the Shapley operator, state by state.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L183-L188
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L183-L188

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.twoGame_fixed : ∀ s, (twoGame.toDiscountedCSG twoGame_wf).shapley
    (fun s' => ((vStar s' : ℚ) : ℝ)) s = ((vStar s : ℚ) : ℝ) := by sorry

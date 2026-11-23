-- Prove2me | Theorems.Thm_Comp_twoGame_v2_error
-- name    : Comp.twoGame_v2_error
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:40:51.67091+00:00
-- url     : https://prove2.me/theorems/06a16e73-40e1-49b2-85d3-4dab198baa0b
-- title:
--   Comp: two Game v2 error
-- statement:
--   **An `ε` guarantee for a genuinely computed step.** `v1` and `v2` differ by at most `1/2`, and
--       `2 · l · (1/2) = 1/2 < 1 = 2 · (1 - l)`, so the stopping test fires at `ε = 2` and `v2` is
--       within `1` of the game's value.
--
--       Loose here only because the instance is tiny: with `vOpt true = 2/3` the true error is `1/2`,
--       exactly `l·d/(1-l)`, so the underlying bound in `dist_vOpt_le_of_step` is tight and it is the
--       conversion to a strict `ε` that gives up the slack. The point is that the hypothesis
--       `2 * l * d < ε * (1 - l)` is a comparison of rationals, discharged below by `norm_num` rather
--       than searched for.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L243-L248
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L243-L248

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.twoGame_v2_error :
    2 * dist (fun s => ((v2 s : ℚ) : ℝ)) (twoGame.toDiscountedCSG twoGame_wf).vOpt
      < ((2 : ℚ) : ℝ) := by sorry

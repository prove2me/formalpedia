-- Prove2me | Theorems.Thm_Comp_stage_true_A
-- name    : Comp.stage_true_A
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:35:47.131271+00:00
-- url     : https://prove2.me/theorems/2ff981eb-53f5-4ac8-af25-c83b416b0b3e
-- title:
--   Comp: stage true A
-- statement:
--   The live state's payoff matrix: `l` times the continuation at whichever state the pair of
--       actions sends the game to. Matching-pennies-shaped whenever `v true < v false`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L106-L109
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L106-L109

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.stage_true_A (v : Bool → ℚ) (a1 a2 : Bool) :
    (twoGame.shapleyGameQ true v).A a1 a2 = 1 / 2 * (if a1 = a2 then v true else v false) := by sorry

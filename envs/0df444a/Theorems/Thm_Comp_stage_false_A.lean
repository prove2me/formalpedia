-- Prove2me | Theorems.Thm_Comp_stage_false_A
-- name    : Comp.stage_false_A
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:35:46.778523+00:00
-- url     : https://prove2.me/theorems/7ff31015-4931-4fdd-b5be-d87939df421b
-- title:
--   Comp: stage false A
-- statement:
--   The absorbing state's payoff matrix is constant: the actions are irrelevant there.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L112-L114
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean#L112-L114

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.stage_false_A (v : Bool → ℚ) (a1 a2 : Bool) :
    (twoGame.shapleyGameQ false v).A a1 a2 = 1 + 1 / 2 * v false := by sorry

-- Prove2me | Theorems.Thm_Comp_rps_value
-- name    : Comp.rps_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:34:44.186829+00:00
-- url     : https://prove2.me/theorems/3da0d20d-4979-4686-b0e8-d96fa0eb4c06
-- title:
--   Comp: rps value
-- statement:
--   **The value of rock-paper-scissors is zero**, as a statement about the real-valued
--       `MatrixGame.value` of `MatrixGame.lean` -- not about a rational approximation of it. The
--       equality is exact because a rational matrix game has a rational value.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/RockPaperScissorsQ.lean#L111-L112
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/RockPaperScissorsQ.lean#L111-L112

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Comp_RockPaperScissorsQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.rps_value : rpsMatrixQ.toMatrixGame.value = 0 := by sorry

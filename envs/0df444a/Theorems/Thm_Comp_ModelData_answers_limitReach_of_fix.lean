-- Prove2me | Theorems.Thm_Comp_ModelData_answers_limitReach_of_fix
-- name    : Comp.ModelData.answers_limitReach_of_fix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:23:29.553498+00:00
-- url     : https://prove2.me/theorems/85c946bf-a8da-4a7d-8f7b-d7e285155447
-- title:
--   Model Data: answers limit Reach of fix
-- statement:
--   **The value-1 set of a model, as an answer to an objective, from one equality.** The states from
--       which the row player reaches `b` with probability arbitrarily close to one -- computed by three
--       nested loops, each proved to terminate, with no count and no fixed-point check anywhere.
--
--       Compare `answers_limitReach_of_data`: four hypotheses, one of them exponential in `|S|`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L878-L883
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L878-L883

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.answers_limitReach_of_fix [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (b c : Finset (Fin d.nStates))
    (hc : d.lfRegion hs b = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.limitReach b) (Answer.region c) := by sorry

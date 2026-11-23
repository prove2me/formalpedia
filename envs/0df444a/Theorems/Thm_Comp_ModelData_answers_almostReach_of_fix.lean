-- Prove2me | Theorems.Thm_Comp_ModelData_answers_almostReach_of_fix
-- name    : Comp.ModelData.answers_almostReach_of_fix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:17:35.763991+00:00
-- url     : https://prove2.me/theorems/59552bbf-2394-48de-b29a-eb5438a1ed86
-- title:
--   Model Data: answers almost Reach of fix
-- statement:
--   **Almost-sure reachability from a model, with nothing to supply but the answer.** Compare
--       `answers_almostReach_of_data`, which wants an inner count, an inner check, and the outer descent
--       assembled by hand.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L655-L660
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L655-L660

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.answers_almostReach_of_fix [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (b c : Finset (Fin d.nStates))
    (hc : d.afRegion hs b = c) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.almostReach b) (Answer.region c) := by sorry

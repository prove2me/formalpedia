-- Prove2me | Theorems.Thm_Comp_ModelData_afStepF_eq_fun
-- name    : Comp.ModelData.afStepF_eq_fun
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:54:18.802917+00:00
-- url     : https://prove2.me/theorems/0345ded3-fe56-4604-96e6-7fc66c0a846c
-- title:
--   Model Data: af Step F eq fun
-- statement:
--   The Model Data construction uses the af Step F eq fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L553-L556
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L553-L556

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.afStepF_eq_fun [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    d.toCsgQ.afStepF b y = d.afStepOf hs b y := by sorry

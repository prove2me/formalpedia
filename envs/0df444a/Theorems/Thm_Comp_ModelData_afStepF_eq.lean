-- Prove2me | Theorems.Thm_Comp_ModelData_afStepF_eq
-- name    : Comp.ModelData.afStepF_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:43:22.522088+00:00
-- url     : https://prove2.me/theorems/4c56e385-629c-4a9e-a2c9-59c4118e78b4
-- title:
--   Model Data: af Step F eq
-- statement:
--   The Model Data construction uses the af Step F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L547-L551
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L547-L551

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.afStepF_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (b y x : Finset (Fin d.nStates)) :
    d.toCsgQ.afStepF b y x = d.afStepOf hs b y x := by sorry

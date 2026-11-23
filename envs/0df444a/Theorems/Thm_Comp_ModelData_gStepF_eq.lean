-- Prove2me | Theorems.Thm_Comp_ModelData_gStepF_eq
-- name    : Comp.ModelData.gStepF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:41:59.33179+00:00
-- url     : https://prove2.me/theorems/e2a56c65-5988-4435-ae85-d9c6eff850fa
-- title:
--   Model Data: g Step F eq
-- statement:
--   The Model Data construction uses the g Step F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L115-L119
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L115-L119

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.gStepF_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (safe x : Finset (Fin d.nStates)) :
    d.toCsgQ.gStepF safe x = d.gStepOf hs safe x := by sorry

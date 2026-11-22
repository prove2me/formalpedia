-- Prove2me | Theorems.Thm_Comp_ModelData_aF_eq
-- name    : Comp.ModelData.aF_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:46:33.836076+00:00
-- url     : https://prove2.me/theorems/8ed9b259-d064-4df2-89e9-ff40b511fc39
-- title:
--   Model Data: a F eq
-- statement:
--   The Model Data construction uses the a F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L481-L486
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L481-L486

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.aF_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) :
    d.toCsgQ.aF v2 y s = d.aOf hs v2 y s := by sorry

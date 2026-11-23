-- Prove2me | Theorems.Thm_Comp_ModelData_gStepF_eq_fun
-- name    : Comp.ModelData.gStepF_eq_fun
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:53:31.020278+00:00
-- url     : https://prove2.me/theorems/cc2bdf77-1204-42ed-8e81-2e0be42bbf65
-- title:
--   Model Data: g Step F eq fun
-- statement:
--   The same, as an equality of *functions*, which is the form a rewrite inside
--       `Function.iterate` needs.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L123-L126
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L123-L126

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.gStepF_eq_fun [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (safe : Finset (Fin d.nStates)) :
    d.toCsgQ.gStepF safe = d.gStepOf hs safe := by sorry

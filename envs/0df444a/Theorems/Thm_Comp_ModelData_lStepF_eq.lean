-- Prove2me | Theorems.Thm_Comp_ModelData_lStepF_eq
-- name    : Comp.ModelData.lStepF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:46:45.971812+00:00
-- url     : https://prove2.me/theorems/0f91143c-2578-4ccd-8f71-629f37e9cb95
-- title:
--   Model Data: l Step F eq
-- statement:
--   The Model Data construction uses the l Step F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L514-L519
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L514-L519

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.lStepF_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    d.toCsgQ.lStepF x y s = d.lStepOf hs x y s := by sorry

-- Prove2me | Theorems.Thm_Comp_ModelData_coe_afStepOf
-- name    : Comp.ModelData.coe_afStepOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:21:36.018068+00:00
-- url     : https://prove2.me/theorems/52fccb33-0d8b-4011-a35a-85b200a0359c
-- title:
--   Model Data: coe af Step Of
-- statement:
--   The inner step over the rows is `AFInner`, under `Finset.coe`: the bridge for the inner loop.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L621-L625
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L621-L625

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.coe_afStepOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y x : Finset (Fin d.nStates)) :
    (↑(d.afStepOf hs b y x) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).AFInner ↑b ↑y ↑x := by sorry

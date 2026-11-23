-- Prove2me | Theorems.Thm_Comp_ModelData_coe_lStepOf
-- name    : Comp.ModelData.coe_lStepOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:29.415799+00:00
-- url     : https://prove2.me/theorems/8f06e4b7-22d6-48d2-a6a4-c931de3c3bce
-- title:
--   Model Data: coe l Step Of
-- statement:
--   The innermost step over the rows is `CSG.LStep`, under `Finset.coe`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L812-L817
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L812-L817

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.coe_lStepOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates)
    (w : Finset (Fin d.nAct1)) :
    (↑(d.lStepOf hs x y s w) : Set (Fin d.nAct1))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).LStep ↑x ↑y s ↑w := by sorry

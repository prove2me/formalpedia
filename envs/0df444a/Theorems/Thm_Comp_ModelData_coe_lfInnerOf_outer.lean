-- Prove2me | Theorems.Thm_Comp_ModelData_coe_lfInnerOf_outer
-- name    : Comp.ModelData.coe_lfInnerOf_outer
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:22:58.93928+00:00
-- url     : https://prove2.me/theorems/62a5986b-3b73-4dd3-9152-838206008c7c
-- title:
--   Model Data: coe lf Inner Of outer
-- statement:
--   …and `LFOuter` *is* that least fixed point, so the middle loop is the outer loop's bridge. One
--       `rfl`, kept separate so the definitional step sits in one place.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L855-L859
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L855-L859

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.coe_lfInnerOf_outer [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    (↑(d.lfInnerOf hs b y) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).LFOuter ↑b ↑y := by sorry

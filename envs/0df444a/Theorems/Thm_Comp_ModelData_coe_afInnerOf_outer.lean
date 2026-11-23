-- Prove2me | Theorems.Thm_Comp_ModelData_coe_afInnerOf_outer
-- name    : Comp.ModelData.coe_afInnerOf_outer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:21:45.651883+00:00
-- url     : https://prove2.me/theorems/8aeeb22e-640a-40b6-9a72-0fef03e2bd87
-- title:
--   Model Data: coe af Inner Of outer
-- statement:
--   …and `AFOuter` *is* that least fixed point, so the inner loop is the outer loop's bridge. The
--       restatement is one `rfl`; it is separate only to keep the definitional step in one place.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L637-L641
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L637-L641

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.coe_afInnerOf_outer [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    (↑(d.afInnerOf hs b y) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).AFOuter ↑b ↑y := by sorry

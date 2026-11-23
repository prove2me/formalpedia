-- Prove2me | Theorems.Thm_Comp_ModelData_coe_afInnerOf
-- name    : Comp.ModelData.coe_afInnerOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:21:39.806546+00:00
-- url     : https://prove2.me/theorems/6d005d8a-b78b-44ba-8724-040e94b55261
-- title:
--   Model Data: coe af Inner Of
-- statement:
--   The inner loop lands on `AFInner`'s least fixed point -- unconditionally, by
--       `lfp_eq_coe_fixFrom_empty`. This is the step that makes the nesting possible.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L629-L633
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L629-L633

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.coe_afInnerOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    (↑(d.afInnerOf hs b y) : Set (Fin d.nStates))
      = ((d.toCsgQ.toCSG (d.wellFormed hs h2)).AFInner ↑b ↑y).lfp := by sorry

-- Prove2me | Theorems.Thm_Comp_ModelData_coe_lfInnerOf
-- name    : Comp.ModelData.coe_lfInnerOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:56.613737+00:00
-- url     : https://prove2.me/theorems/760894fa-4271-4bad-bd27-b03c695a525f
-- title:
--   Model Data: coe lf Inner Of
-- statement:
--   The middle loop lands on `LFInner`'s least fixed point.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L847-L851
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L847-L851

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.coe_lfInnerOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) :
    (↑(d.lfInnerOf hs b y) : Set (Fin d.nStates))
      = ((d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y).lfp := by sorry

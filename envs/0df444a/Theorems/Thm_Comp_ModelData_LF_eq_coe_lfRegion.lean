-- Prove2me | Theorems.Thm_Comp_ModelData_LF_eq_coe_lfRegion
-- name    : Comp.ModelData.LF_eq_coe_lfRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:57.981964+00:00
-- url     : https://prove2.me/theorems/949874b7-bff4-4e1a-9f40-06170cc2f7c8
-- title:
--   Model Data: LF eq coe lf Region
-- statement:
--   **Where the three loops stop *is* `CSG.LF b`.** Unconditionally.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L867-L871
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L867-L871

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.LF_eq_coe_lfRegion [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b : Finset (Fin d.nStates)) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LF ↑b
      = (↑(d.lfRegion hs b) : Set (Fin d.nStates)) := by sorry

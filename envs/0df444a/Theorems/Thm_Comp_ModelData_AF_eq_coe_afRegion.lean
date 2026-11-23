-- Prove2me | Theorems.Thm_Comp_ModelData_AF_eq_coe_afRegion
-- name    : Comp.ModelData.AF_eq_coe_afRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:21:52.340177+00:00
-- url     : https://prove2.me/theorems/0fedadd0-453f-4a68-849b-2f73aaf992d5
-- title:
--   Model Data: AF eq coe af Region
-- statement:
--   **Where the nested loops stop *is* the almost-sure reachability set.** Unconditionally: the
--       outer descent's upper-bound chain from `gfp_le_coe_fixAux`, its termination from
--       `fixFrom_univ_fixed`, and the inner fixed point from `coe_afInnerOf`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L646-L650
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L646-L650

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.AF_eq_coe_afRegion [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b : Finset (Fin d.nStates)) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).AF ↑b
      = (↑(d.afRegion hs b) : Set (Fin d.nStates)) := by sorry

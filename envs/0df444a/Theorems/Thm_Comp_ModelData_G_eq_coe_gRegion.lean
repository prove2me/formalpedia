-- Prove2me | Theorems.Thm_Comp_ModelData_G_eq_coe_gRegion
-- name    : Comp.ModelData.G_eq_coe_gRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:20:06.834867+00:00
-- url     : https://prove2.me/theorems/996438f0-fb8c-442b-9356-dcff92a01364
-- title:
--   Model Data: G eq coe g Region
-- statement:
--   **Where the loop stops *is* the sure-safety region.** Unconditionally: the downward half comes
--       from `Comp/FixLoop.lean`'s `gfp_le_coe_fixAux`, one `OrderHom.gfp_le_of_step` per level of fuel,
--       and the upward half from `fixFrom_univ_fixed`, which proves that `Fintype.card S` steps always
--       reach a fixed point. Nothing is counted and nothing is checked -- `coe_gStepOf` is the only
--       input, and even the monotonicity `fixFrom_univ_fixed` needs comes out of it.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L176-L180
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L176-L180

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.G_eq_coe_gRegion [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (safe : Finset (Fin d.nStates)) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).G (↑safe : Set (Fin d.nStates))
      = (↑(d.gRegion hs safe) : Set (Fin d.nStates)) := by sorry

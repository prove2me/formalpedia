-- Prove2me | Theorems.Thm_Comp_ModelData_coe_gStepOf
-- name    : Comp.ModelData.coe_gStepOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:19:47.821079+00:00
-- url     : https://prove2.me/theorems/7d8033c3-6597-464a-82cc-c69df013a140
-- title:
--   Model Data: coe g Step Of
-- statement:
--   The step over the rows is the specification's own `GOrderHom`, under `Finset.coe`. This is the
--       `hf` that `Comp/FixLoop.lean`'s lemmas take -- the single bridge between the loop and the
--       real-valued game, and the only place the three transfer lemmas are needed.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L165-L169
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L165-L169

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.coe_gStepOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (safe x : Finset (Fin d.nStates)) :
    (↑(d.gStepOf hs safe x) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).GOrderHom ↑safe ↑x := by sorry

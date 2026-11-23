-- Prove2me | Theorems.Thm_Comp_ModelData_LW_eq_of_data
-- name    : Comp.ModelData.LW_eq_of_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:17:25.923384+00:00
-- url     : https://prove2.me/theorems/4c236ef3-d5d7-498b-a9a8-80f5367e574a
-- title:
--   Model Data: LW eq of data
-- statement:
--   The row-action witness set at `s`, once the inner iteration has been seen to stop: `LW`, from
--       the rows.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L698-L705
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L698-L705

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.LW_eq_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates)
    (hfix : d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅) = (d.lStepOf hs x y s)^[k] ∅) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LW ↑x ↑y s
      = (↑((d.lStepOf hs x y s)^[k] ∅) : Set (Fin d.nAct1)) := by sorry

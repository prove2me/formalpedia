-- Prove2me | Theorems.Thm_Comp_ModelData_LW_eq_coe_lwOf
-- name    : Comp.ModelData.LW_eq_coe_lwOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:50.092873+00:00
-- url     : https://prove2.me/theorems/158809f2-d2b1-4cf4-954a-bdcc706a3131
-- title:
--   Model Data: LW eq coe lw Of
-- statement:
--   **`LW`, with no check at all.** Compare `LW_eq_of_data`, which wants `hfix` at this `(x, y, s)`;
--       over all `x` that hypothesis is what made the limit-sure line exponential.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L821-L825
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L821-L825

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.LW_eq_coe_lwOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LW ↑x ↑y s
      = (↑(d.lwOf hs x y s) : Set (Fin d.nAct1)) := by sorry

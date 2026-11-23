-- Prove2me | Theorems.Thm_Comp_ModelData_apre1Tr_eq
-- name    : Comp.ModelData.apre1Tr_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:24:25.473326+00:00
-- url     : https://prove2.me/theorems/4ba3b51c-d18c-4521-a917-b9a9b2f90ee9
-- title:
--   Model Data: apre1 Tr eq
-- statement:
--   **`Apre1`, narrowed.** Three steps and every side condition is free: `aTr_eq` at `v2 = ∅`
--       (pad-saturated by `padSat2_empty`), `bTr_inter_enabled1` on the pad-saturation of an `aF`
--       output, and `bF_eq_univ_iff` to trade `= Finset.univ` for `= enabled2 s`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L431-L438
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L431-L438

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.apre1Tr_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) :
    d.apre1Tr hs x y = d.toCsgQ.apre1F x y := by sorry

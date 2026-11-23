-- Prove2me | Theorems.Thm_Comp_ModelData_AF_le_of_data_step
-- name    : Comp.ModelData.AF_le_of_data_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:17:07.74536+00:00
-- url     : https://prove2.me/theorems/2e41fd6d-5e7c-479a-83b6-03dc49835cb4
-- title:
--   Model Data: AF le of data step
-- statement:
--   One outer step of the `νY` descent. Chained from `CsgQ.AF_le_univ`, once per step.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L577-L583
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L577-L583

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.AF_le_of_data_step [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y c : Finset (Fin d.nStates)) (m : ℕ)
    (hiter : (d.afStepOf hs b y)^[m] ∅ = c) (hfix : d.afStepOf hs b y c = c)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).AF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).AF ↑b ≤ (↑c : Set (Fin d.nStates)) := by sorry

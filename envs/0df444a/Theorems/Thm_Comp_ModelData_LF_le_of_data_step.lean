-- Prove2me | Theorems.Thm_Comp_ModelData_LF_le_of_data_step
-- name    : Comp.ModelData.LF_le_of_data_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:15.928632+00:00
-- url     : https://prove2.me/theorems/5243d990-b2ca-47ad-bfb4-94581d7b6de1
-- title:
--   Model Data: LF le of data step
-- statement:
--   One outer step of the `νY` descent. Chained from `CsgQ.LF_le_univ`, once per step.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L764-L772
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L764-L772

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.LF_le_of_data_step [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (b y c : Finset (Fin d.nStates)) (m : ℕ)
    (hlw : ∀ x s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅)
      = (d.lStepOf hs x y s)^[k] ∅)
    (hiter : (d.midOf hs k b y)^[m] ∅ = c) (hfix : d.midOf hs k b y c = c)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).LF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LF ↑b ≤ (↑c : Set (Fin d.nStates)) := by sorry

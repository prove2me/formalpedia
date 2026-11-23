-- Prove2me | Theorems.Thm_Comp_ModelData_mid_le_of_data
-- name    : Comp.ModelData.mid_le_of_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:10.925244+00:00
-- url     : https://prove2.me/theorems/1b094392-09a4-4ebe-acc3-be775e4b6f20
-- title:
--   Model Data: mid le of data
-- statement:
--   Every stage of the middle climb is a lower bound on the `μX` fixed point.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L724-L741
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L724-L741

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.mid_le_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (b y : Finset (Fin d.nStates)) (m : ℕ)
    (hlw : ∀ x s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅)
      = (d.lStepOf hs x y s)^[k] ∅) :
    (↑((d.midOf hs k b y)^[m] ∅) : Set (Fin d.nStates))
      ≤ ((d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y).lfp := by sorry

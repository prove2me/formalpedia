-- Prove2me | Theorems.Thm_Comp_ModelData_afInner_eq_of_data
-- name    : Comp.ModelData.afInner_eq_of_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:17:07.202428+00:00
-- url     : https://prove2.me/theorems/8a34dfc5-cfab-4b44-86ee-5d33b5ebf424
-- title:
--   Model Data: af Inner eq of data
-- statement:
--   One outer step's inner `μX` fixed point, from a chain run over the rows.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L565-L574
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L565-L574

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.afInner_eq_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y c : Finset (Fin d.nStates)) (m : ℕ)
    (hiter : (d.afStepOf hs b y)^[m] ∅ = c) (hfix : d.afStepOf hs b y c = c) :
    ((d.toCsgQ.toCSG (d.wellFormed hs h2)).AFInner ↑b ↑y).lfp =
      (↑c : Set (Fin d.nStates)) := by sorry

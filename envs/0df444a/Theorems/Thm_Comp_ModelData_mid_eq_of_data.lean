-- Prove2me | Theorems.Thm_Comp_ModelData_mid_eq_of_data
-- name    : Comp.ModelData.mid_eq_of_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:17:23.301336+00:00
-- url     : https://prove2.me/theorems/7d31f3b9-bca5-4913-bce0-6e58c9da5ce8
-- title:
--   Model Data: mid eq of data
-- statement:
--   A middle chain run and seen to stop pins the `μX` fixed point at `y`, exactly.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L744-L759
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L744-L759

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.mid_eq_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (b y c : Finset (Fin d.nStates)) (m : ℕ)
    (hlw : ∀ x s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅)
      = (d.lStepOf hs x y s)^[k] ∅)
    (hiter : (d.midOf hs k b y)^[m] ∅ = c) (hfix : d.midOf hs k b y c = c) :
    ((d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y).lfp =
      (↑c : Set (Fin d.nStates)) := by sorry

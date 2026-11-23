-- Prove2me | Theorems.Thm_Comp_ModelData_answers_almostReach_of_data
-- name    : Comp.ModelData.answers_almostReach_of_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:24:54.761206+00:00
-- url     : https://prove2.me/theorems/8194a4c6-70f5-4ebe-aae7-a7f6d2ce0557
-- title:
--   Model Data: answers almost Reach of data
-- statement:
--   **Almost-sure reachability of `b`, as an answer to an objective.** The outer chain has stopped
--       at `y`: it is its own inner `μX` fixed point, and the descent has reached it. Everything the
--       caller supplies is a `decide` away -- `hiter` and `hfix` are `Finset` equalities over the rows,
--       and `hy` is the chain, one `AF_le_of_data_step` per outer step from `CsgQ.AF_le_univ`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L589-L595
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L589-L595

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.answers_almostReach_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (b y : Finset (Fin d.nStates)) (m : ℕ)
    (hiter : (d.afStepOf hs b y)^[m] ∅ = y) (hfix : d.afStepOf hs b y y = y)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).AF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.almostReach b) (Answer.region y) := by sorry

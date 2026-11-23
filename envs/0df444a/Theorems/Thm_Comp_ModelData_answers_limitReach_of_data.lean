-- Prove2me | Theorems.Thm_Comp_ModelData_answers_limitReach_of_data
-- name    : Comp.ModelData.answers_limitReach_of_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:22.066497+00:00
-- url     : https://prove2.me/theorems/87ec49da-51ee-4446-8971-b0c5c1bc3fd4
-- title:
--   Model Data: answers limit Reach of data
-- statement:
--   **The value-1 set of a model, as an answer to an objective.** `y` is its own certified `μX`
--       fixed point and the outer descent has reached it, so it *is* `CSG.LF b` -- the states from which
--       the row player can reach `b` with probability arbitrarily close to one.
--
--       Four hypotheses, all decidable over the rows: the inner iteration has stopped (`hlw`), the
--       middle chain reached `y` and stays (`hiter`, `hfix`), and the descent got there (`hy`, one
--       `LF_le_of_data_step` per outer step from `CsgQ.LF_le_univ`). Nothing about the real-valued
--       operators is asked of the caller, and nothing in any of it evaluates a weight.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L782-L790
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L782-L790

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.answers_limitReach_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape)
    (h2 : d.Stochastic) (hnz : d.Nonzero) (k : ℕ) (b y : Finset (Fin d.nStates)) (m : ℕ)
    (hlw : ∀ x s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅)
      = (d.lStepOf hs x y s)^[k] ∅)
    (hiter : (d.midOf hs k b y)^[m] ∅ = y) (hfix : d.midOf hs k b y y = y)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).LF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    d.toCsgQ.Answers (d.wellFormed hs h2) (Objective.limitReach b) (Answer.region y) := by sorry

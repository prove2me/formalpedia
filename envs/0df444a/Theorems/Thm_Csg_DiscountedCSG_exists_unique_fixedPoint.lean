-- Prove2me | Theorems.Thm_Csg_DiscountedCSG_exists_unique_fixedPoint
-- name    : Csg.DiscountedCSG.exists_unique_fixedPoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:54:12.317866+00:00
-- url     : https://prove2.me/theorems/5f3f7564-3de3-4042-af9f-6df7185ec309
-- title:
--   Discounted CSG: exists unique fixed Point
-- statement:
--   **The payoff.** The Shapley operator has exactly one fixed point -- the value vector of the
--       discounted concurrent game. Existence is `ContractingWith.exists_fixedPoint` (Banach, over the
--       complete space `S → ℝ`); uniqueness is the same short argument `Mdp/Basic.lean` uses, two
--       fixed points each being a contraction factor away from the other and so at distance `0`.
--       `(0 : S → ℝ)` as the iteration basepoint is arbitrary.
--
--       This is the existence half of Shapley (1953) for the finite discounted case. Note what it does
--       *not* say: nothing here identifies the fixed point with a strategic notion of game value, i.e.
--       with what either coalition can guarantee under optimal play over infinite horizons. That is a
--       separate theorem, and the project has its analogue only for the bounded case
--       (`BackwardInduction.lean`) and for the undiscounted objectives via their own operators.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Discounted.lean#L183-L191
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Discounted.lean#L183-L191

import Definitions.Def_Csg_CsgMonotone
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Csg_Discounted
set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)

theorem Csg.DiscountedCSG.exists_unique_fixedPoint : ∃! v : S → ℝ, D.shapley v = v := by sorry

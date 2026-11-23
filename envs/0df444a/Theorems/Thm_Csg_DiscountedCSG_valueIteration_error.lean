-- Prove2me | Theorems.Thm_Csg_DiscountedCSG_valueIteration_error
-- name    : Csg.DiscountedCSG.valueIteration_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:03:38.359327+00:00
-- url     : https://prove2.me/theorems/2c24c6cb-0906-4cbf-93f4-10a6a51d8fee
-- title:
--   Discounted CSG: value Iteration error
-- statement:
--   **The payoff.** Once value iteration stops (`eps > 0`), its output is within `eps / 2` of the
--       game's value. Mirrors `DiscountedMDP.valueIteration_error` and, through it,
--       `value_iteration_error` in `Value_Iteration.thy`; the proof below is that one with `shapley`
--       for `bellman`.
--
--       This is the statement the whole discounted line exists to reach, and the one the undiscounted
--       operators cannot state at all: `ReachConverge.lean` has convergence without a rate, so it can
--       say the iterates approach the value but never that a particular iterate is within a given
--       distance of it. See the module docstring on why an exactness result is not available here even
--       in principle.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/DiscountedValueIteration.lean#L168-L199
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/DiscountedValueIteration.lean#L168-L199

import Definitions.Def_Csg_Discounted
import Definitions.Def_Csg_DiscountedValueIteration
set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)

theorem Csg.DiscountedCSG.valueIteration_error {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    2 * dist (D.valueIteration eps v) D.vOpt < eps := by sorry

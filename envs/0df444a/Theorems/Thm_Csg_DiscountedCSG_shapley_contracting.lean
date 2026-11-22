-- Prove2me | Theorems.Thm_Csg_DiscountedCSG_shapley_contracting
-- name    : Csg.DiscountedCSG.shapley_contracting
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:46:07.417362+00:00
-- url     : https://prove2.me/theorems/28768844-77e1-4471-aece-bd4379c35c77
-- title:
--   Discounted CSG: shapley contracting
-- statement:
--   **The theorem this file exists for.** The Shapley operator is an `l`-Lipschitz contraction in
--       sup distance -- the concurrent-game analogue of `contraction_ℒ` as ported in
--       `Mdp/Basic.lean`'s `bellman_contracting`, and the fact that makes a *terminating* value
--       iteration possible for discounted concurrent games where the undiscounted operators admit no
--       stopping bound at all.
--
--       Same three moves as the MDP proof: `dist_pi_le_iff` turns the goal into a per-state bound,
--       `dist_le_pi_dist` supplies that state's pointwise hypothesis from the ambient `dist v u`, and
--       `shapley_lipschitz` does the work in between. Shapley's own 1953 argument is this contraction
--       plus Banach; the contraction is the part that needs the game theory, and it is exactly where
--       `MatrixGame.abs_value_sub_le` is doing the work a `sup'` does for free in the MDP case.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Discounted.lean#L150-L157
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Discounted.lean#L150-L157

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

theorem Csg.DiscountedCSG.shapley_contracting (v u : S → ℝ) :
    dist (D.shapley v) (D.shapley u) ≤ D.l * dist v u := by sorry

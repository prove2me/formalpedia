-- Prove2me | Theorems.Thm_Comp_DiscountedCsgQ_two_dist_vOpt_lt_of_step
-- name    : Comp.DiscountedCsgQ.two_dist_vOpt_lt_of_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:34:59.951799+00:00
-- url     : https://prove2.me/theorems/ddddabe0-8b45-47b1-8ada-31e44cb228b9
-- title:
--   Discounted Csg Q: two dist v Opt lt of step
-- statement:
--   **The payoff: a checkable stopping test.** Under the *rational* condition
--       `2 * l * d < ε * (1 - l)`, the computed iterate `w` is within `ε / 2` of the game's value.
--
--       The hypothesis is the rational twin of `Csg/DiscountedValueIteration.lean`'s `stopCond`, and
--       that is the whole point: `stopCond` is a statement about real distances that `numIters` must
--       search for, while this one is a comparison of rationals that `norm_num` settles on the spot. The
--       conclusion is `valueIteration_error`'s, for one computed step rather than for an abstract
--       iteration.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Iterate.lean#L182-L200
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Iterate.lean#L182-L200

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_DiscountedValueIteration
import Definitions.Def_Comp_Iterate
set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.DiscountedCsgQ.two_dist_vOpt_lt_of_step (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed)
    {v w : S → ℚ} {d eps : ℚ} (hd0 : 0 ≤ d) (hd : ∀ s, |v s - w s| ≤ d)
    (hstep : ∀ s, (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s
      = ((w s : ℚ) : ℝ))
    (hstop : 2 * G.l * d < eps * (1 - G.l)) :
    2 * dist (fun s => ((w s : ℚ) : ℝ)) (G.toDiscountedCSG h).vOpt < ((eps : ℚ) : ℝ) := by sorry

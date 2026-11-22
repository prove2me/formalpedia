-- Prove2me | Theorems.Thm_Comp_DiscountedCsgQ_dist_vOpt_le_of_step
-- name    : Comp.DiscountedCsgQ.dist_vOpt_le_of_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:34:56.16743+00:00
-- url     : https://prove2.me/theorems/9557df1b-4baf-4549-a004-40dd8fa8cf37
-- title:
--   Discounted Csg Q: dist v Opt le of step
-- statement:
--   **The a posteriori bound for a computed step.** If `w` is the Shapley image of `v` and the two
--       differ by at most `d` at every state, the distance from `w` to the game's value is at most
--       `l * d / (1 - l)`.
--
--       Assembled from three facts already in `Csg/`: `shapley_aposteriori_bound` at `n = 0` bounds
--       `v`'s own error by the step it takes, `shapley_contracting` at `vOpt` (a fixed point, by
--       `vOpt_fixedPoint`) transfers that bound to `w` with a factor `l`, and `dist_cast_le` gives the
--       rational bound on the step. The arithmetic is cleared of denominators with `le_div_iff₀` before
--       `nlinarith`, the same route `valueIteration_error` takes.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Iterate.lean#L148-L172
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Iterate.lean#L148-L172

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_DiscountedValueIteration
import Definitions.Def_Comp_Iterate
set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.DiscountedCsgQ.dist_vOpt_le_of_step (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed)
    {v w : S → ℚ} {d : ℚ} (hd0 : 0 ≤ d) (hd : ∀ s, |v s - w s| ≤ d)
    (hstep : ∀ s, (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s
      = ((w s : ℚ) : ℝ)) :
    dist (fun s => ((w s : ℚ) : ℝ)) (G.toDiscountedCSG h).vOpt
      ≤ (G.toDiscountedCSG h).l * ((d : ℚ) : ℝ) / (1 - (G.toDiscountedCSG h).l) := by sorry

-- Prove2me | Theorems.Thm_Comp_DiscountedCsgQ_eq_vOpt_of_fixed
-- name    : Comp.DiscountedCsgQ.eq_vOpt_of_fixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:34:45.777698+00:00
-- url     : https://prove2.me/theorems/260116c6-4f46-4ab0-9638-c176474000bd
-- title:
--   Discounted Csg Q: eq v Opt of fixed
-- statement:
--   **The exact route, when it is available.** A rational vector that the Shapley operator fixes
--       *is* the game's value -- no error term. The operator is a contraction
--       (`Csg/Discounted.lean`'s `contractingWith_shapley`), so its fixed point is unique, and
--       exhibiting one therefore identifies `vOpt` outright.
--
--       This fires only when the value happens to be rational, which for a concurrent game is luck
--       rather than the rule -- the fixed point is algebraic and generally irrational. When it does
--       fire it is strictly better than any `ε` bound, so it is worth trying before settling for one.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Iterate.lean#L122-L126
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Iterate.lean#L122-L126

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_DiscountedValueIteration
import Definitions.Def_Comp_Iterate
set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.DiscountedCsgQ.eq_vOpt_of_fixed (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) {v : S → ℚ}
    (hfix : ∀ s, (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s
      = ((v s : ℚ) : ℝ)) :
    (fun s => ((v s : ℚ) : ℝ)) = (G.toDiscountedCSG h).vOpt := by sorry

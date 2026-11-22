-- Prove2me | Theorems.Thm_Comp_DiscountedCsgQ_dist_cast_le
-- name    : Comp.DiscountedCsgQ.dist_cast_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:34:46.018701+00:00
-- url     : https://prove2.me/theorems/e923b405-b378-4ae3-a3bf-166414ff0be6
-- title:
--   Discounted Csg Q: dist cast le
-- statement:
--   A pointwise rational bound gives a bound on the sup distance between the casts. `0 ≤ d` is
--       carried explicitly rather than recovered from `hd`, because `S` is not assumed `Nonempty` and so
--       there need not be any state at which to read the sign off.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Iterate.lean#L131-L137
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Iterate.lean#L131-L137

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_DiscountedValueIteration
import Definitions.Def_Comp_Iterate
set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.DiscountedCsgQ.dist_cast_le {v w : S → ℚ} {d : ℚ} (hd0 : 0 ≤ d) (hd : ∀ s, |v s - w s| ≤ d) :
    dist (fun s => ((v s : ℚ) : ℝ)) (fun s => ((w s : ℚ) : ℝ)) ≤ ((d : ℚ) : ℝ) := by sorry

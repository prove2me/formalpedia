-- Prove2me | Theorems.Thm_Comp_DiscountedCsgQ_shapleyGameQ_A_cast
-- name    : Comp.DiscountedCsgQ.shapleyGameQ_A_cast
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:11:34.512867+00:00
-- url     : https://prove2.me/theorems/73f94ee9-25ba-45a7-aace-dc4cb3a9a3c1
-- title:
--   Discounted Csg Q: shapley Game Q A cast
-- statement:
--   The entries of the two stage games agree under the cast: the real operator's payoff at a joint
--       action is the cast of the rational one's. The reward term casts directly, and the expectation
--       term is `CsgQ.expect_toCSG`; `push_cast` then moves the cast across the sum and product.
--
--       Written with `change` to put both sides in their unfolded form first -- the projections through
--       `extends` (`toDiscountedCSG`'s `toCSG`, and that structure's `r`) all reduce definitionally, but
--       `rw` will not fire against them until they do.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Shapley.lean#L66-L76
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Shapley.lean#L66-L76

import Definitions.Def_Comp_Search
import Definitions.Def_Comp_Shapley
set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.DiscountedCsgQ.shapleyGameQ_A_cast (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) (s : S) (v : S → ℚ)
    (a1 : A1) (a2 : A2) :
    ((G.toDiscountedCSG h).shapleyGame s (fun s' => ((v s' : ℚ) : ℝ))).A a1 a2
      = ((G.shapleyGameQ s v).toMatrixGame).A a1 a2 := by sorry

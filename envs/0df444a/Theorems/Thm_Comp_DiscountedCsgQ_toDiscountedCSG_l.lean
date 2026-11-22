-- Prove2me | Theorems.Thm_Comp_DiscountedCsgQ_toDiscountedCSG_l
-- name    : Comp.DiscountedCsgQ.toDiscountedCSG_l
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:40:46.511366+00:00
-- url     : https://prove2.me/theorems/a24e9d38-4fba-4264-b8c6-d31cabac692f
-- title:
--   Discounted Csg Q: to Discounted CSG l
-- statement:
--   The discount of `toDiscountedCSG` is the cast of the rational one. Also `rfl`, and recorded for
--       the same reason: it is needed wherever a rational iteration's discount factor has to be matched
--       against the real-valued operator's.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Basic.lean#L199-L200
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Basic.lean#L199-L200

import Definitions.Def_Csg_Discounted
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Comp_Basic
set_option autoImplicit true
open Comp
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Comp.DiscountedCsgQ

theorem Comp.DiscountedCsgQ.toDiscountedCSG_l (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) :
    (G.toDiscountedCSG h).l = ((G.l : ℚ) : ℝ) := by sorry

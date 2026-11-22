-- Prove2me | Theorems.Thm_Csg_DiscountedCSG_vOpt_fixedPoint
-- name    : Csg.DiscountedCSG.vOpt_fixedPoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:32:31.913568+00:00
-- url     : https://prove2.me/theorems/3e1603f4-3ea1-4134-a8ad-5ee47e0c71e3
-- title:
--   Discounted CSG: v Opt fixed Point
-- statement:
--   `vOpt` really is a fixed point of `shapley` -- the Shapley equations hold at it.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/DiscountedValueIteration.lean#L80-L81
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/DiscountedValueIteration.lean#L80-L81

import Definitions.Def_Csg_Discounted
import Definitions.Def_Csg_DiscountedValueIteration
set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)

theorem Csg.DiscountedCSG.vOpt_fixedPoint : D.shapley D.vOpt = D.vOpt := by sorry

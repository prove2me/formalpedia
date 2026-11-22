-- Prove2me | Theorems.Thm_Csg_DiscountedCSG_exists_unique_fixedPoint_choose_eq_vOpt
-- name    : Csg.DiscountedCSG.exists_unique_fixedPoint_choose_eq_vOpt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:32:47.576234+00:00
-- url     : https://prove2.me/theorems/b3d2e871-d0bf-4fb2-9766-9345885888a1
-- title:
--   Discounted CSG: exists unique fixed Point choose eq v Opt
-- statement:
--   `vOpt` and `Csg/Discounted.lean`'s `exists_unique_fixedPoint` witness are the same function:
--       both are *the* unique fixed point of `shapley`, reached through different Mathlib entry
--       points.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/DiscountedValueIteration.lean#L86-L88
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/DiscountedValueIteration.lean#L86-L88

import Definitions.Def_Csg_Discounted
import Definitions.Def_Csg_DiscountedValueIteration
import Theorems.Thm_Csg_DiscountedCSG_exists_unique_fixedPoint

set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)

theorem Csg.DiscountedCSG.exists_unique_fixedPoint_choose_eq_vOpt :
    D.exists_unique_fixedPoint.choose = D.vOpt := by sorry

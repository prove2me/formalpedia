-- Prove2me | Theorems.Thm_FRI_prod_tail_zero
-- name    : FRI_prod_tail_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:03:31.971831+00:00
-- url     : https://prove2.me/theorems/86eb287c-8b6a-413e-8900-1255080c4ac0
-- title:
--   FRI prod tail zero: FRI prod tail zero
-- statement:
--   FRI_prod_tail 0 equals the full product
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L418-L420
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L418-L420

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_prod_tail_zero {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) :
    FRI_prod_tail P 0 = ∏ j, P.m j := by sorry

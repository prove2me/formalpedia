-- Prove2me | Theorems.Thm_FRI_prod_tail_ge
-- name    : FRI_prod_tail_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:20:25.980936+00:00
-- url     : https://prove2.me/theorems/abb98e0b-3d36-4d26-a1c7-2e418aefd20a
-- title:
--   FRI prod tail ge: FRI prod tail ge
-- statement:
--   FRI_prod_tail for i ≥ num_foldings equals 1
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L423-L429
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L423-L429

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_prod_tail_ge {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F)
    (i : ℕ) (hi : P.num_foldings ≤ i) :
    FRI_prod_tail P i = 1 := by sorry

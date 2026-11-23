-- Prove2me | Theorems.Thm_FRI_prod_tail_split
-- name    : FRI_prod_tail_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:56:29.818453+00:00
-- url     : https://prove2.me/theorems/64b23af5-c353-450e-97b3-5238ecfee7e9
-- title:
--   FRI prod tail split: FRI prod tail split
-- statement:
--   FRI_prod_tail splits as m_i * FRI_prod_tail (i+1)
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L432-L445
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L432-L445

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_prod_tail_split {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : ℕ) (hi : i < P.num_foldings) :
    FRI_prod_tail P i = P.m ⟨i, hi⟩ * FRI_prod_tail P (i + 1) := by sorry

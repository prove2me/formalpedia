-- Prove2me | Theorems.Thm_FRI_distance_star_lt_one_sub_bound
-- name    : FRI_distance_star_lt_one_sub_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:32:20.537546+00:00
-- url     : https://prove2.me/theorems/2d007faa-b38e-4362-8a4e-c8ed9cc38d6b
-- title:
--   FRI distance star lt one sub bound: FRI distance star lt one sub bound
-- statement:
--   The FRI distance star lt one sub bound construction uses the FRI distance star lt one sub bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L362-L368
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L362-L368

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_distance_star_lt_one_sub_bound {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) :
    FRI_distance_star P f_0 bound < 1 - bound := by sorry

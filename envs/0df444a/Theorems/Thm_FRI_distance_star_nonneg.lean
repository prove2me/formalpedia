-- Prove2me | Theorems.Thm_FRI_distance_star_nonneg
-- name    : FRI_distance_star_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:10:26.165923+00:00
-- url     : https://prove2.me/theorems/eb890e8f-0cb4-4fc0-b9cb-e670893e75c3
-- title:
--   FRI distance star nonneg: FRI distance star nonneg
-- statement:
--   The FRI distance star nonneg construction uses the FRI distance star nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L662-L666
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L662-L666

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_distance_star_nonneg (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (h_bound_valid : bound + 1 / P.D_0.card ≤ 1) :
    0 ≤ FRI_distance_star P f_0 bound := by sorry

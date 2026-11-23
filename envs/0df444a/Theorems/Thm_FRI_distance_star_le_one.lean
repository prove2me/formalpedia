-- Prove2me | Theorems.Thm_FRI_distance_star_le_one
-- name    : FRI_distance_star_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:29:03.512593+00:00
-- url     : https://prove2.me/theorems/7a4d7796-695e-443f-8673-691ec8848401
-- title:
--   FRI distance star le one: FRI distance star le one
-- statement:
--   The FRI distance star le one construction uses the FRI distance star le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L671-L682
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L671-L682

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_distance_star_le_one (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) :
    FRI_distance_star P f_0 bound ≤ 1 := by sorry

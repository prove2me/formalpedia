-- Prove2me | Theorems.Thm_FRI_BadEvent_eq_Folding_Bad_Event
-- name    : FRI_BadEvent_eq_Folding_Bad_Event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:07:23.624801+00:00
-- url     : https://prove2.me/theorems/14b632c7-2c9a-42d8-b1f9-ac584d8b424b
-- title:
--   FRI Bad Event eq Folding Bad Event: FRI Bad Event eq Folding Bad Event
-- statement:
--   The FRI Bad Event eq Folding Bad Event construction uses the FRI Bad Event eq Folding Bad Event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L181-L204
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L181-L204

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_BadEvent_eq_Folding_Bad_Event (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (i : Fin P.num_foldings) (f_prev : FRI_domain P i → F) (alpha : F) :
    FRI_BadEvent P f_0 bound i f_prev alpha ↔
    Folding_Bad_Event (FRI_domain P i) (P.m i) (FRI_degree P i)
      f_prev alpha (FRI_distance_star P f_0 bound) := by sorry

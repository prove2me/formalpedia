-- Prove2me | Theorems.Thm_FRI_BadEvent_implies_MCA_BadEvent
-- name    : FRI_BadEvent_implies_MCA_BadEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:32:10.298194+00:00
-- url     : https://prove2.me/theorems/b4dcf47b-668d-4fdb-9c59-3f6628de3a8a
-- title:
--   FRI Bad Event implies MCA Bad Event: FRI Bad Event implies MCA Bad Event
-- statement:
--   The FRI Bad Event implies MCA Bad Event construction uses the FRI Bad Event implies MCA Bad Event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L283-L310
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L283-L310

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_BadEvent_implies_MCA_BadEvent {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (i : Fin P.num_foldings) (f_prev : FRI_domain P i → F) (alpha : F) :
    FRI_BadEvent P f_0 bound i f_prev alpha →
    BadEvent (FRI_code P (i.succ)) (P.m i) (cast_folding_components P i f_prev)
      (FRI_distance_star P f_0 bound) (fun j ↦ alpha ^ (j : ℕ)) := by sorry

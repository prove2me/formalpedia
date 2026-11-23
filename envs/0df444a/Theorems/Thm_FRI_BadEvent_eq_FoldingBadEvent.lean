-- Prove2me | Theorems.Thm_FRI_BadEvent_eq_FoldingBadEvent
-- name    : FRI_BadEvent_eq_FoldingBadEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:07:25.7019+00:00
-- url     : https://prove2.me/theorems/8268f763-9041-447d-baa2-c41aa58627f9
-- title:
--   FRI Bad Event eq Folding Bad Event: FRI Bad Event eq Folding Bad Event
-- statement:
--   The FRI Bad Event eq Folding Bad Event construction uses the FRI Bad Event eq Folding Bad Event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L332-L344
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L332-L344

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_BadEvent_eq_FoldingBadEvent
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (i : Fin P.num_foldings) (f_prev : FRI_domain P i → F) (alpha : F) :
    FRI_BadEvent P f_0 bound i f_prev alpha ↔
    FoldingBadEvent (FRI_domain P i) (P.m i) (FRI_code P i) (FRI_code_cast P i i.isLt)
      (extend_by_zero (FRI_domain P i) f_prev) (FRI_distance_star P f_0 bound) alpha := by sorry

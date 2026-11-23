-- Prove2me | Theorems.Thm_FRI_fold_agreement_on_W
-- name    : FRI_fold_agreement_on_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:09:50.748333+00:00
-- url     : https://prove2.me/theorems/412e72e9-fcf7-49ca-9311-6eafe3216334
-- title:
--   FRI fold agreement on W: FRI fold agreement on W
-- statement:
--   The FRI fold agreement on W construction uses the FRI fold agreement on W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L559-L611
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L559-L611

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_fold_agreement_on_W
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (i : Fin P.num_foldings) :
    ∀ z ∈ FRI_W P f_0 T (i + 1),
      Fold (FRI_domain P i) (P.m i)
        (extend_by_zero (FRI_domain P i) (FRI_oracle_at_round P f_0 T i i.isLt)) (T.alpha i) z =
      extend_by_zero (FRI_domain P (i.val + 1)) (T.f i) z := by sorry

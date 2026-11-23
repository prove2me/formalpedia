-- Prove2me | Theorems.Thm_FRI_agreement_next_implies_fold_agreement
-- name    : FRI_agreement_next_implies_fold_agreement
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:13:38.447676+00:00
-- url     : https://prove2.me/theorems/7ee697ef-e313-482e-b74c-a399423473fc
-- title:
--   FRI agreement next implies fold agreement: FRI agreement next implies fold agreement
-- statement:
--   The FRI agreement next implies fold agreement construction uses the FRI agreement next implies fold agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L263-L304
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L263-L304

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_green_set_pow_subset

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_agreement_next_implies_fold_agreement (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) (i : Fin P.num_foldings)
    (h_agree_next : FRI_agreement_at_round P f_0 T i.succ) :
    ∃ u' ∈ FRI_code P i.succ, ∀ z (hz : z ∈ pow_domain (FRI_green_set P f_0 T i) (P.m i)),
      let f_prev := extend_by_zero (FRI_domain P i) (fun x ↦ FRI_get_val P f_0 T i.castSucc x)
      Fold (FRI_domain P i) (P.m i) f_prev (T.alpha i) z =
        u' ⟨z, FRI_green_set_subset_domain P f_0 T i.succ
          (FRI_green_set_pow_subset P f_0 T i i.isLt hz)⟩ := by sorry

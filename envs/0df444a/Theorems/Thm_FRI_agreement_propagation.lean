-- Prove2me | Theorems.Thm_FRI_agreement_propagation
-- name    : FRI_agreement_propagation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:13:39.562359+00:00
-- url     : https://prove2.me/theorems/c72090df-6f55-4e06-b752-a9d128e9ebc8
-- title:
--   FRI agreement propagation: FRI agreement propagation
-- statement:
--   The FRI agreement propagation construction uses the FRI agreement propagation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L309-L366
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L309-L366

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_agreement_propagation (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (i : Fin P.num_foldings)
    (h_not_bad : ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i))
    (h_large : FRI_Is_Large_Subset P f_0 bound i i.isLt (FRI_green_set P f_0 T i.castSucc))
    (h_agree_next : FRI_agreement_at_round P f_0 T i.succ) :
    FRI_agreement_at_round P f_0 T i.castSucc := by sorry

-- Prove2me | Theorems.Thm_FRI_State_succ_iff_verifier_accepts
-- name    : FRI_State_succ_iff_verifier_accepts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:01:14.964844+00:00
-- url     : https://prove2.me/theorems/1aa073db-d718-42bb-9624-fb76ea0cc1dc
-- title:
--   FRI State succ iff verifier accepts: FRI State succ iff verifier accepts
-- statement:
--   The FRI State succ iff verifier accepts construction uses the FRI State succ iff verifier accepts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L494-L499
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L494-L499

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_State_succ_iff_verifier_accepts (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings) :
    FRI_State P f_0 bound T (P.num_foldings + 1) ↔ FRI_verifier_accepts P f_0 T := by sorry

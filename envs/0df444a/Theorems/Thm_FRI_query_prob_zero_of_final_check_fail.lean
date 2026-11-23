-- Prove2me | Theorems.Thm_FRI_query_prob_zero_of_final_check_fail
-- name    : FRI_query_prob_zero_of_final_check_fail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:14:13.985556+00:00
-- url     : https://prove2.me/theorems/113b1dab-bee9-4d54-b9a2-94b560045147
-- title:
--   FRI query prob zero of final check fail: FRI query prob zero of final check fail
-- statement:
--   The FRI query prob zero of final check fail construction uses the FRI query prob zero of final check fail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L504-L520
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L504-L520

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_query_prob_zero_of_final_check_fail [Fintype F] [MeasurableSpace F]
    [DiscreteMeasurableSpace F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings)
    (h_fail : FRI_final_oracle P f_0 T ∉ FRI_code P P.num_foldings) :
    FRI_query_prob P f_0 bound T = 0 := by sorry

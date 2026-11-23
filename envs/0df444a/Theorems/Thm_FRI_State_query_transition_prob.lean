-- Prove2me | Theorems.Thm_FRI_State_query_transition_prob
-- name    : FRI_State_query_transition_prob
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:39:01.644317+00:00
-- url     : https://prove2.me/theorems/bcbad382-930c-426a-aeb2-8cf1a6a0078b
-- title:
--   FRI State query transition prob: FRI State query transition prob
-- statement:
--   State 0 → 1 transition at query round: probability equals verifier acceptance probability
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L110-L113
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L110-L113

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
omit [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]

theorem FRI_State_query_transition_prob (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (h_state_0 : ¬ FRI_State P f_0 bound T P.num_foldings) :
    FRI_State P f_0 bound T (P.num_foldings + 1) ↔ FRI_verifier_accepts P f_0 T := by sorry

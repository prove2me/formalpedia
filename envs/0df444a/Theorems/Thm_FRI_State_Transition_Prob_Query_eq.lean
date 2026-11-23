-- Prove2me | Theorems.Thm_FRI_State_Transition_Prob_Query_eq
-- name    : FRI_State_Transition_Prob_Query_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:16:54.69907+00:00
-- url     : https://prove2.me/theorems/e49a8f89-dafc-47be-ac3e-abf2dd9706e7
-- title:
--   FRI State Transition Prob Query eq: FRI State Transition Prob Query eq
-- statement:
--   When State(k) = 0, the query transition probability equals the query probability
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L163-L167
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L163-L167

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
omit [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]

theorem FRI_State_Transition_Prob_Query_eq [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) (T : FRITranscript P)
    (h_state_0 : ¬ FRI_State P f_0 bound T P.num_foldings) :
    FRI_State_Transition_Prob_Query P f_0 bound T = FRI_query_prob P f_0 bound T := by sorry

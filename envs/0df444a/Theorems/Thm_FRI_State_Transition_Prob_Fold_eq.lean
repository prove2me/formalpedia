-- Prove2me | Theorems.Thm_FRI_State_Transition_Prob_Fold_eq
-- name    : FRI_State_Transition_Prob_Fold_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:17:04.447776+00:00
-- url     : https://prove2.me/theorems/2a5b83c4-a961-4bab-a0a3-ae2027da33b0
-- title:
--   FRI State Transition Prob Fold eq: FRI State Transition Prob Fold eq
-- statement:
--   When State(i) = 0, the fold transition probability equals the bad event probability
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L153-L159
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L153-L159

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
omit [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]

theorem FRI_State_Transition_Prob_Fold_eq [Fintype F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) (T : FRITranscript P)
    (i : Fin P.num_foldings)
    (h_state_0 : ¬ FRI_State P f_0 bound T i) :
    FRI_State_Transition_Prob_Fold P f_0 bound T i =
      FRI_BadEvent_Prob P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) := by sorry

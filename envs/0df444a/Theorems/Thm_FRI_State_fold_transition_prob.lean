-- Prove2me | Theorems.Thm_FRI_State_fold_transition_prob
-- name    : FRI_State_fold_transition_prob
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:38:08.724857+00:00
-- url     : https://prove2.me/theorems/982674e9-a7d7-4d77-990b-9b8aa7aa0191
-- title:
--   FRI State fold transition prob: FRI State fold transition prob
-- statement:
--   State 0 → 1 transition at folding round i: probability is bounded by bad event probability
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L101-L106
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean#L101-L106

import Definitions.Def_SimpleRbrFri_QuerySoundness
import Definitions.Def_SimpleRbrFri_Soundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
omit [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]

theorem FRI_State_fold_transition_prob (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (i : Fin P.num_foldings)
    (h_state_0 : ¬ FRI_State P f_0 bound T i) :
    FRI_State P f_0 bound T (i + 1) ↔
    FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i) := by sorry

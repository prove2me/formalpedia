-- Prove2me | Theorems.Thm_FRI_State_false_implies_no_bad_event
-- name    : FRI_State_false_implies_no_bad_event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:00:43.296267+00:00
-- url     : https://prove2.me/theorems/add84863-a42c-430b-9ddf-aae6327e880f
-- title:
--   FRI State false implies no bad event: FRI State false implies no bad event
-- statement:
--   The FRI State false implies no bad event construction uses the FRI State false implies no bad event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L394-L400
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L394-L400

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_State_false_implies_no_bad_event (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (h_state : ¬ FRI_State P f_0 bound T P.num_foldings) :
    ∀ i : Fin P.num_foldings,
      ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i) := by sorry

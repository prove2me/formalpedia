-- Prove2me | Theorems.Thm_FRI_claim_queryphase_if_domain_large_induction
-- name    : FRI_claim_queryphase_if_domain_large_induction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:11:50.09844+00:00
-- url     : https://prove2.me/theorems/f1cea35f-9ba7-49aa-b5f4-f5fc061442c5
-- title:
--   FRI claim queryphase if domain large induction: FRI claim queryphase if domain large induction
-- statement:
--   The FRI claim queryphase if domain large induction construction uses the FRI claim queryphase if domain large induction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L130-L153
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L130-L153

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true

theorem FRI_claim_queryphase_if_domain_large_induction
    {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_f_final : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings)
    (h_W_large : ∀ i : Fin (P.num_foldings + 1),
        (FRI_W P f_0 T i).card ≥ (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i).card)
    (h_no_bad : ∀ i : Fin P.num_foldings,
        ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i)) :
    ∀ i : Fin (P.num_foldings + 1), ∃ u ∈ FRI_code P i, ∀ x ∈ FRI_W P f_0 T i,
      extend_by_zero (FRI_domain P i) (FRI_f P f_0 T i) x =
        extend_by_zero (FRI_domain P i) u x := by sorry

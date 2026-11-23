-- Prove2me | Theorems.Thm_FRI_claim_queryphase_if_domain_large
-- name    : FRI_claim_queryphase_if_domain_large
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:12:32.876318+00:00
-- url     : https://prove2.me/theorems/6d7d5723-28a9-4c93-b33a-cfd1a2e3ab22
-- title:
--   FRI claim queryphase if domain large: FRI claim queryphase if domain large
-- statement:
--   The FRI claim queryphase if domain large construction uses the FRI claim queryphase if domain large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L166-L184
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L166-L184

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_W_subset_domain
import Theorems.Thm_FRI_domain_zero_eq_D0

set_option autoImplicit true

theorem FRI_claim_queryphase_if_domain_large
    {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_f_final : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings)
    (h_W_large : ∀ i : Fin (P.num_foldings + 1),
        (FRI_W P f_0 T i).card ≥ (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i).card)
    (h_no_bad : ∀ i : Fin P.num_foldings,
        ¬ FRI_BadEvent P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt) (T.alpha i)) :
    ∃ u_0 ∈ FRI_code P 0, ∀ x (hx : x ∈ FRI_W P f_0 T 0),
      u_0 ⟨x, FRI_W_subset_domain P f_0 T 0 hx⟩ =
      f_0 ⟨x, FRI_domain_zero_eq_D0 P ▸ FRI_W_subset_domain P f_0 T 0 hx⟩ := by sorry

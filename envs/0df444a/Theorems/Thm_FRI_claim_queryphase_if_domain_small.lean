-- Prove2me | Theorems.Thm_FRI_claim_queryphase_if_domain_small
-- name    : FRI_claim_queryphase_if_domain_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:09:47.695768+00:00
-- url     : https://prove2.me/theorems/fa93b268-cd05-4a35-a827-fc8553a253f8
-- title:
--   FRI claim queryphase if domain small: FRI claim queryphase if domain small
-- statement:
--   The FRI claim queryphase if domain small construction uses the FRI claim queryphase if domain small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L509-L535
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L509-L535

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_claim_queryphase_if_domain_small (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) (bound : ℝ)
    (h_domain_size : FRI_Domain_Size_Property P)
    (i_star : Fin (P.num_foldings + 1))
    (h_small : (FRI_W P f_0 T i_star).card <
      (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i_star).card)
    (h_D_pos : ∀ i : Fin (P.num_foldings + 1), (FRI_domain P i).card > 0) :
    (FRI_W P f_0 T 0).card < (1 - FRI_distance_star P f_0 bound) * (FRI_domain P 0).card := by sorry
